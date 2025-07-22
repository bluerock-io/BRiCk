exception Test_exc

let _ =
  Printf.printf "Printexc.backtrace_status: %b\n" (Printexc.backtrace_status());
  raise Test_exc
