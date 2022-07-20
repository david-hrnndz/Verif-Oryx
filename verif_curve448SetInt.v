Require Import VST.floyd.proofauto.
Require Import curve448.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Local Open Scope Z.

Definition curve448SetInt_spec : ident * funspec :=
DECLARE _curve448SetInt
WITH a : val,
     sha : share,
     contents_a : list val,
     b : Z,
     gv : globals
PRE [ tptr tuint, tuint ]
    PROP   (writable_share sha;
            Zlength contents_a = 14)
    PARAMS (a ; Vint(Int.repr b)) GLOBALS (gv)
    SEP    (data_at sha (tarray tuint 14) contents_a a)
POST [ tvoid ]
    PROP   ()
    RETURN ()
    SEP    (data_at sha (tarray tuint 14) (map Vint (map Int.repr (b :: (Zrepeat 0 13)))) a).

Definition curve448SetInt_INV a sha contents_a b := 
(EX i : Z,
(PROP   (writable_share sha; 
        Zlength contents_a = 14)
LOCAL   (temp _a a)
SEP     (data_at sha (tarray tuint 14) 
            ([Vint (Int.repr b)] ++ (Zrepeat (Vint (Int.repr 0)) (i-1)) ++
              sublist.sublist i 14 contents_a) a
        )))%assert.

Lemma L1 (h x : val) (l : list val) (i : Z) :
1 <= i -> upd_Znth i ([h] ++ l) x = [h] ++ (upd_Znth (i-1) l) x.
Proof. intros. list_simplify. Qed.

Lemma L2 (i : Z) (l1 l2 : list val) (x : val) :
Zlength l1 <= i ->
upd_Znth i (l1 ++ l2) x = l1 ++ (upd_Znth (i-(Zlength l1)) l2) x.
Proof. intros. list_simplify. Qed.

Lemma L3 (x h : val) (l : list val):
upd_Znth 0 ([h] ++ l) x  = [x] ++ l.
Proof. list_simplify. Qed.

Definition Gprog : funspecs := ltac:(with_library prog [ curve448SetInt_spec ]).

Lemma body_curve448SetInt : semax_body Vprog Gprog f_curve448SetInt curve448SetInt_spec.
Proof.
    start_function.
    forward.
    forward_for_simple_bound 14 (curve448SetInt_INV a sha contents_a b).
    -   entailer!.
        replace (upd_Znth 0 contents_a (Vint (Int.repr b))) with ([Vint (Int.repr b)] ++
        Zrepeat (Vint (Int.repr 0)) (1 - 1) ++ sublist.sublist 1 14 contents_a)
        by list_simplify; cancel.
    -   forward.
        entailer!.
        replace (upd_Znth i ([Vint (Int.repr b)] ++ Zrepeat (Vint (Int.repr 0)) (i - 1) 
        ++ sublist.sublist i 14 contents_a) (Vint (Int.repr 0))) with 
        ([Vint (Int.repr b)] ++ Zrepeat (Vint (Int.repr 0)) (i + 1 - 1) ++
        sublist.sublist (i + 1) 14 contents_a) by list_simplify; cancel.
    -   entailer!.
        replace ([Vint (Int.repr b)] ++
        Zrepeat (Vint (Int.repr 0)) (14 - 1) ++ sublist.sublist 14 14 contents_a) with 
        (Vint (Int.repr b) :: map Vint (map Int.repr (Zrepeat 0 13))) by list_simplify;
        cancel.
Qed.
