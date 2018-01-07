
let run ct cf : unit =
  begin
    List.fold_left (fun _ c -> print_char c) () (run_test ct cf);
    print_newline ()
  end
                
let main() = begin

    if (compare "store" Sys.argv.(1)) = 0
    then
      if (compare "undef" Sys.argv.(2)) = 0
      then run CStore EqualUndefAllowed
      else
        if (compare "def" Sys.argv.(2)) = 1
        then run CStore EqualNoUndef
        else run CStore TestSpecific
    else
      if (compare "jump" Sys.argv.(1)) = 0
      then
        if (compare "undef" Sys.argv.(2)) = 0
        then run CJump EqualUndefAllowed
        else
          if (compare "def" Sys.argv.(2)) = 1
          then run CJump EqualNoUndef
          else run CJump TestSpecific
      else
        if (compare "stack" Sys.argv.(1)) = 0
        then
          if (compare "undef" Sys.argv.(2)) = 0
          then run CStack EqualUndefAllowed
          else
            if (compare "def" Sys.argv.(2)) = 1
            then run CStack EqualNoUndef
            else run CStack TestSpecific
        else
          if (compare "correct" Sys.argv.(1)) = 0
          then
            if (compare "undef" Sys.argv.(2)) = 0
            then run CCompCorrect EqualUndefAllowed
            else
              if (compare "def" Sys.argv.(2)) = 1
              then run CCompCorrect EqualNoUndef
              else run CCompCorrect TestSpecific
          else
            print_string "error: Missing or incorrect argument";
  end;;

main();
