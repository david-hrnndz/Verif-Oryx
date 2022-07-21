Require Import VST.floyd.proofauto.
Require Import curve448.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Local Open Scope Z.

Scheme Equality for list.

Definition curve448Comp_spec : ident * funspec :=
DECLARE _curve448Comp
WITH a : val, contents_a : list Z,
     b : val, contents_b : list Z,
     gv : globals
PRE [ tptr tuint, tptr tuint ]
    PROP   (Zlength contents_a = 14;
            Zlength contents_b = 14)
    PARAMS ( a; b ) GLOBALS (gv)
    SEP    (data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_b)) b)
POST [ tuint ]
    PROP   ()
    RETURN (if (list_beq Z Z.eqb contents_a contents_b) then Vint Int.zero else Vint Int.one)
    SEP    (data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_b)) b).


Definition Comp (i : Z) (a b : list Z) : int := 
    if (list_beq Z Z.eqb (sublist.sublist 0 i a) (sublist.sublist 0 i b))
    then Int.zero else Int.one.



(* AQUIIIIIIIIIIIIIIIIII *)

Lemma L : list_beq Z Z.eqb (sublist.sublist 0 (i + 1) l1)
(sublist.sublist 0 (i + 1) l2) = true ->
list_beq Z Z.eqb (sublist.sublist 0 i l1) (sublist.sublist 0 i l2) = true /\ 
Zinth i l1 = Zinth i l2.


Definition curve448Comp_INV a contents_a b contents_b := 
(EX i : Z,
(PROP   (Zlength contents_a = 14;
         Zlength contents_b = 14)
LOCAL   (temp _a a; temp _b b; temp _mask (Vint (Comp i contents_a contents_b)))
SEP     (data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a;
         data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_b)) b
        )))%assert.

Definition Gprog : funspecs := ltac:(with_library prog [ curve448Comp_spec ]).

Lemma body_curve448Comp : semax_body Vprog Gprog f_curve448Comp curve448Comp_spec.
Proof.
    start_function.
    forward.
    forward_for_simple_bound 14 
    (curve448Comp_INV a contents_a b contents_b).
    -   entailer!.
    -   repeat forward.
        entailer!.
        apply f_equal.
        unfold Comp.
        destruct (list_beq Z Z.eqb (sublist.sublist 0 (i + 1) contents_a)
        (sublist.sublist 0 (i + 1) contents_b)) eqn:E.
        unfold list_beq in E.0
        inversion E.
        Search "lxor" inside Z.

        simpl.
        replace (0 - 1) with (-1) by lia.
        rewrite Z.land_m1_r.
        replace (Int.not (Int.repr (-1))) with (Int.zero) by easy.
        rewrite Int.and_zero, Int.or_zero.
        autorewrite with sublist.
        replace (sublist.sublist 0 i (map Vint (map Int.repr contents_a)) ++
        upd_Znth 0 (sublist.sublist i 14 contents_r)
        (Vint (Int.repr (Znth i contents_a))))
        with  
        (sublist.sublist 0 (i + 1) (map Vint (map Int.repr contents_a)) ++
        sublist.sublist (i + 1) 14 contents_r)
        by list_simplify; cancel.
    -   entailer!.
        simpl. 
        autorewrite with sublist; cancel.
    * (* Case c = 0 *)
    forward.
    forward_for_simple_bound 14 
    (curve448Comp_INV r shr contents_r a contents_a b contents_b c);
    rewrite H2; autorewrite with norm.
    -   entailer!.
        simpl; autorewrite with sublist; cancel.
    -   repeat forward. 
        entailer!.
        simpl.
        replace (1 - 1) with 0 by lia.
        rewrite Z.land_0_r.
        unfold Int.not.
        rewrite Int.xor_zero_l, Int.and_mone, Int.or_zero_l.
        replace (upd_Znth i
        (sublist.sublist 0 i (map Vint (map Int.repr contents_b)) ++
         sublist.sublist i 14 contents_r) (Vint (Int.repr (Znth i contents_b))))
        with 
        (sublist.sublist 0 (i + 1) (map Vint (map Int.repr contents_b)) ++
        sublist.sublist (i + 1) 14 contents_r)
        by list_simplify; cancel.
    -   entailer!.
        simpl.
        autorewrite with sublist; cancel.   
Qed.
