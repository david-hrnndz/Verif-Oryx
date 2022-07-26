Require Import VST.floyd.proofauto.
Require Import curve448.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Local Open Scope Z.

Compute reptype (tarray tuint 14).
Definition curve448Copy_spec : ident * funspec :=
DECLARE _curve448Copy
WITH  a : val, sha : share, contents_a : list val, (* Destination integer (editable) *)
      b : val, contents_b : list Z,              (* Source integer *)
      gv : globals
PRE [ tptr tuint, tptr tuint ]
    PROP   (writable_share sha;
            Zlength contents_a = 14;
            Zlength contents_b = 14)
    PARAMS (a ; b) GLOBALS (gv)
    SEP    (data_at sha (tarray tuint 14) contents_a a;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr (contents_b))) b)
POST [ tvoid ]
    PROP   ()
    RETURN ()
    SEP    (data_at sha (tarray tuint 14) (map Vint (map Int.repr (contents_b))) a;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr (contents_b))) b).

Definition curve448Copy_INV a sha contents_a b contents_b := 
   (EX i : Z,
   (PROP   (writable_share sha; 
            Zlength contents_a = 14;
            Zlength contents_b = 14)
   LOCAL   (temp _a a; temp _b b)
   SEP     (data_at sha (tarray tuint 14) 
               (  sublist.sublist 0 i (map Vint (map Int.repr (contents_b))) 
               ++ sublist.sublist i 14 contents_a) a ;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr (contents_b))) b
            )))%assert.

Definition Gprog : funspecs := ltac:(with_library prog [ curve448Copy_spec ]).

Lemma body_curve448SetInt : semax_body Vprog Gprog f_curve448Copy curve448Copy_spec.
Proof.
(* Initialize everything. *)
start_function. 
(* Get loop started. *)
forward_for_simple_bound 14 (curve448Copy_INV a sha contents_a b contents_b).
(* Show PRE implies INV. *)
entailer!.
autorewrite with sublist.
list_simplify.

(* Step through loop. *)
forward.
forward.
(* Show INV is actually INV as the loop happens. *)
entailer!.
autorewrite with sublist.
list_simplify.

(* Show INV implies POST. *)
entailer!.
autorewrite with sublist.
list_simplify.
Qed.