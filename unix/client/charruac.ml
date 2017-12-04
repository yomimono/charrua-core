(*
 * Copyright (c) 2015 Christiano F. Haesbaert <haesbaert@haesbaert.org>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *)

open Lwt.Infix


let () = Printexc.record_backtrace true

let filter_map f l = List.rev @@
  List.fold_left (fun a v -> match f v with Some v' -> v'::a | None -> a) [] l

let level_of_string = function
  | "warning" -> Lwt_log.Warning
  | "notice" -> Lwt_log.Notice
  | "debug" -> Lwt_log.Debug
  | _ -> invalid_arg "Unknown verbosity level"

(* Drop privileges and chroot to _charruac home *)
let go_safe () =
  let (pw, gr) = try
      (Unix.getpwnam "_charruac", Unix.getgrnam "_charruac")
    with _  ->
      failwith "No user and/or group _charruac found, please create them."
  in
  Unix.chroot pw.Unix.pw_dir;
  Unix.chdir "/";
  (* Unix.setproctitle "charruad"; XXX implement me *)
  let ogid = Unix.getgid () in
  let oegid = Unix.getegid () in
  let ouid = Unix.getuid () in
  let oeuid = Unix.geteuid () in
  Unix.setgroups (Array.of_list [pw.Unix.pw_gid]);
  Unix.setgid pw.Unix.pw_gid;
  Unix.setuid pw.Unix.pw_uid;
  if ogid = pw.Unix.pw_gid ||
     oegid = pw.Unix.pw_gid ||
     ouid = pw.Unix.pw_uid ||
     oeuid = pw.Unix.pw_uid then
    failwith "Unexpected uid or gid after dropping privileges";
  (* Make sure we cant restore the old gid and uid *)
  let canrestore = try
      Unix.setuid ouid;
      Unix.setuid oeuid;
      Unix.setgid ogid;
      Unix.setgid oegid;
      true
    with _ -> false in
  if canrestore then
    failwith "Was able to restore UID, setuid is broken"

let read_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let buf = Bytes.create n in
  really_input ic buf 0 n;
  close_in ic;
  Bytes.to_string buf

let go_daemon () =
  Lwt_daemon.daemonize ~syslog:false ()

let init_log vlevel daemon =
  Lwt_log_core.Section.(set_level main vlevel);
  Lwt_log.default := if daemon then
      Lwt_log.syslog
        ~template:"$(date) $(level) $(name)[$(pid)]: $(message)"
        ~facility:`Daemon
        ~paths:["/dev/log"; "/var/run/log"; "/var/run/syslog"]
        ()
    else
      Lwt_log.channel
        ~template:"$(date) $(level): $(message)"
        ~close_mode:`Keep
        ~channel:Lwt_io.stdout
        ()

let ifname_of_address ip_addr interfaces =
  let ifnet =
    List.find (function name, (ip_addrx, _) -> ip_addr = ip_addrx) interfaces
  in
  match ifnet with name, (_, _) -> name

module Mirage_net_rawlink_lwt : sig
  include Mirage_net_lwt.S 
  val connect : string -> bool -> t list
end = struct
  type t = { rawlink : Lwt_rawlink.t; mac : Macaddr.t }
  type stats = Mirage_net.stats
  type 'a io = 'a Lwt.t
  type macaddr = Macaddr.t
  type buffer = Cstruct.t
  type page_aligned_buffer = Io_page.t
  type error = Mirage_device.error
  let pp_error = Mirage_device.pp_error
  let reset_stats_counters _ = ()
  let get_stats_counters _ = Mirage_net.{ rx_bytes = 0L; tx_bytes = 0L;
                                          rx_pkts = 0l; tx_pkts = 0l; }
  let mac t = t.mac
  let listen t fn =
    let rec aux t = 
      Lwt_rawlink.read_packet t.rawlink >>= fn >>= fun () ->
      aux t
    in
    aux t
  let writev t packets = Lwt_list.iter_s (Lwt_rawlink.send_packet t.rawlink)
      packets >>= fun () -> Lwt.return (Ok ())
  let write t packet = Lwt_rawlink.send_packet t.rawlink packet >>= fun () ->
    Lwt.return (Ok ())
  let disconnect _ = Lwt.return_unit
  let connect verbosity daemonize =
    init_log (level_of_string verbosity) daemonize;
    let interfaces = Tuntap.getifaddrs_v4 () in
    let addresses = List.map
        (function name, (addr, _) -> (addr, Tuntap.get_macaddr name))
        interfaces
    in
    if daemonize then
      go_daemon ();
    Lwt_log.ign_notice "Charrua DHCPC starting";
    (* Filter out the addresses which have networks assigned *)
    let links = filter_map
        (fun addr_tuple ->
           let addr = fst addr_tuple in
           let s = Ipaddr.V4.to_string addr in
           Lwt_log.ign_notice_f "Found network for %s" s;
           (* Get a rawlink on the interface *)
           let ifname = ifname_of_address addr interfaces in
           let link = Lwt_rawlink.(open_link ~filter:(dhcp_client_filter ()) ifname) in
           (* Create a thread *)
           Some {rawlink = link; mac = snd addr_tuple}
        ) addresses
    in
    if List.length links = 0 then
      failwith "All interfaces appear to already have addresses"
        (* go_safe (); *)
    ;
    links
end

module Client = Dhcp_client_lwt.Make(Time)(Mirage_net_rawlink_lwt)

let charruac verbosity daemonize =
  let open Lwt in
  match Mirage_net_rawlink_lwt.connect verbosity daemonize with
  | [] -> failwith "Could not find any suitable interface to ask for DHCP on"
  | net::_ ->
    Lwt_main.run (Client.connect net >>= fun lease_stream ->
    Lwt_stream.get lease_stream >>= function
    | None -> Lwt.return_unit
    | Some dhcp -> Lwt_log.info (Dhcp_wire.pkt_to_string dhcp) >>= fun () ->
      Lwt.return_unit)

(* Parse command line and start the ball *)
open Cmdliner
let cmd =
  let verbosity = Arg.(value & opt string "notice" & info ["v" ; "verbosity"]
                         ~doc:"Log verbosity, warning|notice|debug") in
  let daemonize = Arg.(value & flag & info ["D" ; "daemon"]
                         ~doc:"Daemonize") in
  Term.(pure charruac $ verbosity $ daemonize),
  Term.info "charruac" ~version:"0.1" ~doc:"Charrua DHCPC"
let () = match Term.eval cmd with `Error _ -> exit 1 | _ -> exit 0
