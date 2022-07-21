Require Import VST.floyd.proofauto.
Require Import curve448.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Local Open Scope Z.

Definition curve448Select_spec : ident * funspec :=
DECLARE _curve448Select
WITH r : val, shr : share, contents_r : list val,
     a : val, contents_a : list Z,
     b : val, contents_b : list Z,
     c : Z,
     gv : globals
PRE [ tptr tuint, tptr tuint, tptr tuint, tuint ]
    PROP   (writable_share shr;
            Zlength contents_r = 14;
            Zlength contents_a = 14;
            Zlength contents_b = 14;
            c = 0 \/ c = 1)
    PARAMS (r ; a ; b ; Vint(Int.repr c)) GLOBALS (gv)
    SEP    (data_at shr (tarray tuint 14) contents_r r;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_b)) b)
POST [ tvoid ]
    PROP   ()
    RETURN ()
    SEP    (data_at shr (tarray tuint 14) (map Vint (map Int.repr 
                (if (Z.to_nat c) then contents_a else contents_b))) r;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_b)) b).

Definition curve448Select_INV r shr (contents_r : list val) a contents_a b contents_b c := 
(EX i : Z,
(PROP   (writable_share shr; 
         Zlength contents_r = 14;
         Zlength contents_a = 14;
         Zlength contents_b = 14)
LOCAL   (temp _r r; temp _a a; temp _b b; temp _mask (Vint(Int.repr (c-1))))
SEP     (data_at shr (tarray tuint 14) 
            (sublist.sublist 0 i (map Vint (map Int.repr 
              (if (Z.to_nat c) then contents_a else contents_b)))
            ++ sublist.sublist i 14 contents_r) r;
        data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a;
        data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_b)) b
        )))%assert.

Definition Gprog : funspecs := ltac:(with_library prog [ curve448Select_spec ]).

Lemma body_curve448Select : semax_body Vprog Gprog f_curve448Select curve448Select_spec.
Proof.
    start_function.
    destruct H2.
    * (* Case c = 0 *)
    forward.
    forward_for_simple_bound 14 
    (curve448Select_INV r shr contents_r a contents_a b contents_b c);
    rewrite H2; autorewrite with norm.
    -   entailer!.
        autorewrite with sublist; cancel.
    -   repeat forward.
        entailer!.
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
    (curve448Select_INV r shr contents_r a contents_a b contents_b c);
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
