open Run_test

let run run_test : unit =
begin
    List.fold_left (fun _ c -> print_char c) () (run_test);
    print_newline ()
end

let main() = begin
print_string "Run store test\n";
print_newline ();
run run_store_test;
run run_jump_test;
run run_stack_test;
end;;

main();
