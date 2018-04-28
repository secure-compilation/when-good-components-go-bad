open Run_test

let run run_test : unit =
begin
    List.fold_left (fun _ c -> print_char c) () (run_test);
    print_newline ()
end

let main() =
  begin
    run run_store_test;
    run run_jump_test;
    run run_stack_test;
    run run_rsc_test;
  end;;

main();
