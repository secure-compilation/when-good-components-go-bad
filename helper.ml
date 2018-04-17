(* Download https://raw.githubusercontent.com/coq/coq/master/plugins/extraction/big.ml and 
   copy it to your /tmp/ folder. *)

#mod_use "big.ml";;
#use "run_compiled_program.ml";;

let compiled = encode (precompile program1);;

let instr n = List.nth compiled n;;
let decode_mem = (fun x -> concrete_int_32_ops.decode_instr ((snd x).vala));;

let print_word w = let Word x = Lazy.force w in Big.to_string x;;
let print_pc (st : Symbolic.state) = print_word (st.pc.vala);;

let st = load compiled;;

let step = stepf sym_lrc lrc_syscalls;;

print_word (st.pc.vala);;













(* OUTDATED *)
stepf sym_lrc lrc_syscalls st;; (* None! why?  *) 

(* The first instruction is a JAL *)
let Some (Jal w) = decode_mem instr1;;
let Word w = Lazy.force w in Big.to_string w;; (* Jumps to value stored in Register 1 *)

let reg_content = getm (word_ordType mt.reg_field_size) st.regs (Obj.magic w);;
let Some reg_value = reg_content;;
let Word x = Lazy.force (reg_value.vala) in Big.to_string x;; (* 0: is this what we want?? *)



(* executing stepf *)

stepf sym_lrc lrc_syscalls st;;
(* - : Symbolic.state option = None *)

(* step-by-step: *)
let { Symbolic.mem = mem0; Symbolic.regs = reg1; Symbolic.pc = pc0;
    Symbolic.internal = _ } = st;;
let {vala = pc1; taga = tpc0 } = pc0;;

print_word pc1;;
(* - : string = "0" *)

let Some s = getm (word_ordType mt.word_size) mem0 (Obj.magic pc1);;
(* val s : (mword, Equality.sort) atom =
   {vala = lazy (Word <abstr>); taga = <abstr>} *)

let instr = concrete_int_32_ops.decode_instr (s.vala);;
(* val instr : instr0 option = Some (Jal <lazy>) *)

let Some (Jal r) = instr;;
print_word r;;
(* - : string = "1" *)

let a = (getm (word_ordType mt.reg_field_size) reg1 (Obj.magic r));;
(* val a : (mword, Equality.sort) atom option =
 *   Some {vala = <lazy>; taga = <abstr>} *)
let Some { vala = _; taga = t1 } = a;;
(* val t1 : Equality.sort = <abstr> *)

let oldtold = (getm (word_ordType mt.reg_field_size) reg1
                 (Obj.magic ra ((* assert false *) (* Proj Args *)) ops));;
(* val oldtold : (mword, Equality.sort) atom option = None *)




(* /!\ Outdated! now all of this works *)
let encode = concrete_int_32_ops.encode_instr;;
let decode = concrete_int_32_ops.decode_instr;;

let nop = Nop;;
let encoded_nop = encode nop;;
decode encoded_nop;; (* instr0 option = None *)


let const_5_2 = Const (lazy (Word (Big.of_int 5)), lazy (Word (Big.of_int 2))));;
let encoded_const_5_2 = encode const_5_2;;
decode encoded_const_5_2;; (* instr0 option = None *)




(* Step-by-step encoding *)


let opcode = opcode_of concrete_int_32_mt Nop;; (* opcode = NOP *)

let op0 = word_of_op (Big.of_int 5) opcode;;
let Word x = Lazy.force op0 in Big.to_string x;; (* "1" *)

let args = wcast (sumn (fields_of_op opcode)) (Big.of_int 27)
    (wpack (fields_of_op opcode) (args_of_instr Nop));;
let Word x = Lazy.force args in Big.to_string x;; (* "0" *)
(* Correct up to this point *)

let res = wpack ((Big.of_int 5) :: (Big.of_int 27) :: [])
    (Obj.magic (lazy (HSeqCons (op0, (lazy (HSeqCons (args, __))))))))
let Word x = Lazy.force args in Big.to_string x;; (* "16" *)
(* Incorrect.
   16        = 00000000 00000000 00000000 00010000 
   but it should be
   1         = 00000000 00000000 00000000 00000001
   or 
   134217728 = 00001000 00000000 00000000 00000000
*)


(* Step-by-step decoding *)
let to_decode = Big.of_int 1;;
let i' = wunpack ((Big.of_int 5) :: (Big.of_int 27) :: []) (lazy (Word to_decode));;

let op0 = hnth ((Big.of_int 5) :: (Big.of_int 27) :: []) i' Big.zero;;
let Word x = Lazy.force op0 in Big.to_string x;; (* "0" *)
(* Incorrect? it should be "1"?*)

let op1 = hnth ((Big.of_int 5) :: (Big.of_int 27) :: []) i' (Big.succ Big.zero);;
let Word x = Lazy.force op1 in Big.to_string x;;
(* - : string = "67108864" *)
(* ie 100 00000000 00000000 00000000 
   therefore whole number = 00000100 00000000 00000000 00000000
   it seems the number is shifted by one position to the right instead of where it should be!!
   *)


let f = (fun op1 ->
      let args =
        wcast (Big.of_int 27)
          (sumn (fields_of_op op1))
          (hnth ((Big.of_int 5)::(Big.of_int 27)::[]) i' (Big.of_int 1))
      in
      Some (instr_of_args op1 (wunpack (fields_of_op op1) args)));;
(* val f : opcode -> instr0 option *)
f NOP;; (* Some Nop *)
(* function f is correct *)

let s = size ((Big.of_int 5)::(Big.of_int 27)::[]);; (* s = 2 *)
let ns = nat_of_ord s Big.zero;; (* ns = 0 *)


Option.bind f
      (op_of_word
        (nth
           (tag
              (hnth_default ((Big.of_int 5)::(Big.of_int 27)::[]) i' Big.zero))
           ((Big.of_int 5)::(Big.of_int 27)::[]) ns) op0);;
