Require Import List.
Import ListNotations.
(**** Untilities ****)

(* This file defines the syntax of Quantum Abstract Machine.
Var               x,y
Message Name      e
Quantum Channel   c,d
Classical Channel h_c, h_d
Channel           delta := c | h_c
Quantum Message   q := unit | e | c.miu | dagger_q
Classical Message iota := h_q 
Message           miu := q | iota
Contexts          phi := list (c)d.miu      
Action            A := c_down | c_up | h_c!iota_send | delta?(x)_recv 
                      | c encode miu | c!(x)_decode | q!miu(x)_encode | q!(x)_decode
                      | c?(x)_trans 
Process           R,T := 0 | AR | R+T | !R
Raw Membrane      M,N := {|bar_R|}
Membrane          P,Q := {|Bar_R|}phi | R{|Bar_T|}phi | P[(c)d.miu]Q
*)
(*********************************************)
(***      Syntax     ***)
Definition var := nat.

Definition mess_n : Type := nat. (* message name *)
Definition chan_n : Type := nat. (* channel name *)

Definition qchan : Type := chan_n.
Definition cchan : Type := chan_n.
(* Inductive channel:= QC (q : qchan) | CC (c : cchan). *)
Inductive qmess := UNIT | Mess (m : mess_n) | ChanMu (c : chan_m) | PartM (q : qmess)
with      chan_m := MChan (c : qchan) (mu : mess)
with      cmess := MeasureQ (q : qmess)
with      mess   := QtM (q: qmess) | CcM (c: cmess).

Inductive renamedC := RnmC (c : chan_n) (m : chan_m).

Definition contexts  := list renamedC.

Inductive action := CreatC (c : qchan) | QSwap (c : qchan)
               | CSend (cc : cchan) (cm : cmess) | CRecv (cc : cchan) (x : mess_n)
               | LEncode (q : qmess) (mu : mess) (x : mess_n) | LDecode (q : qmess) (x : mess_n)
               | GEncode (c : qchan) (x : mess_n) | GDecode (c : qchan) (x : mess_n)
               | Trans (c : qchan) (x : mess_n).

Inductive process := Nil | AR (a : action) (r : process) | Choice (p : process) (r : process) | Rept (r : process).

Definition rmemb := list process.

Inductive memb := CtxM (r : rmemb) (phi : contexts) | ALock (r : process) (t : rmemb) | ActM (p : memb) (c : renamedC) (Q: memb). 


(***      Semantics   ***)
Fixpoint FC (cx : contexts) :=
  match cx with
  | [] => []
  | ((RnmC c (MChan d m)) :: t) => d :: (FC t)
  end.

