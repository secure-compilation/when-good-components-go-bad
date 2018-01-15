open Run_test

let run ct ig cf : unit =
  begin
    List.fold_left (fun _ c -> print_char c) () (run_test ct ig cf);
    print_newline ()
  end


let get_flag arg : flag = begin
    if (compare "store" arg) = 0
    then TStoreInstrOff
    else
      if (compare "store1" arg) = 0
      then TStoreInstr1Off
      else
        if (compare "store2" arg) = 0
        then TStoreInstr2Off
        else
          if (compare "jump" arg) = 0
          then TJumpInstrOff
          else
            if (compare "jump1" arg) = 0
            then TJumpInstr1Off
            else
              if (compare "jump2" arg) = 0
              then TJumpInstr2Off
              else
                if (compare "push" arg) = 0
                then TPushSfiHaltNotPresent
                else
                  if (compare "pop" arg) = 0
                  then TPopSfiNotAligned
                  else
                    if (compare "call" arg) = 0
                    then TAfterCallLabelMissing
                    else
                      if (compare "targets" arg) = 0
                      then TTargetsNotAligned
                      else TAllOff
  end

let get_checker arg : checker_type = begin
    if (compare "store" arg) = 0
    then CStore
    else
      if (compare "jump" arg) = 0
      then CJump
      else
        if (compare "stack" arg) = 0
        then CStack
        else CCompCorrect
  end

let get_gen arg : instr_gen = begin
    if (compare "undef" arg) = 0
    then EqualUndefAllowed
    else
      if (compare "def" arg) = 0
      then EqualNoUndef
      else TestSpecific
  end

             
let main() = begin
    run (get_checker Sys.argv.(1))
      (get_gen Sys.argv.(2))
      (get_flag Sys.argv.(3))
  end;;

main();
