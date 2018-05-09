open Run_test

let run run_test : unit =
begin
    List.fold_left (fun _ c -> print_char c) () (run_test);
    print_newline ()
end

let main() =
  begin
    run run_mp_test;
  end;;

main();
