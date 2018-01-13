open Run_store_test

let run ct cf : unit =
  begin
    List.fold_left (fun _ c -> print_char c) () (run_store_test ct cf);
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
    
let main() = begin

      if (compare "undef" Sys.argv.(1)) = 0
      then run EqualUndefAllowed (get_flag Sys.argv.(2))
      else
        if (compare "def" Sys.argv.(1)) = 0
        then run EqualNoUndef (get_flag Sys.argv.(2))
        else run TestSpecific (get_flag Sys.argv.(2))

  end;;

main();
