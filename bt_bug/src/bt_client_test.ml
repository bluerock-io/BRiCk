
exception Test_exc

let _ =
  Printf.printf "Printexc.backtrace_status (before using Bt_bug_lib): %b\n" (Printexc.backtrace_status());
  (* ^^ already true! *)
  let _ = Base.compare_option in
  (* ^^ Needed to load the library and trigger the bug *)
  Printf.printf "Printexc.backtrace_status (after using Bt_bug_lib): %b\n" (Printexc.backtrace_status());
  raise Test_exc
