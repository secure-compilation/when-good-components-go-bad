Require Import Common.
Require Import Traces.

Inductive behavior :=
  | BConverges : trace -> behavior
  | BDiverges : trace -> behavior 
  (* | BReact : traceinf -> behavior *) 
  | BGoesWrong : trace -> behavior. 