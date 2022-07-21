Require Import VST.floyd.proofauto.
Require Import curve448.
Require Import list_int_functions.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Local Open Scope Z.


Definition prime: Z := 2^448 - 2^224 - 1.

Definition curve448Red_spec : ident * funspec :=
DECLARE _curve448Red
WITH    r : val,
        shr : share,
        contents_r : list val,   
        a : val,
        contents_a : list Z,
        h : Z, (* may need writable share *)
        gv : globals
PRE [ tptr tuint, tptr tuint, tuint ]
    PROP   (writable_share shr;
            Zlength contents_r = 14;
            Zlength contents_a = 14)
    PARAMS (r ; a ; Vint(Int.repr h)) GLOBALS (gv)
    SEP    (data_at shr (tarray tuint 14) contents_r r;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a)
POST [ tvoid ]
    PROP   ()
    RETURN ()                               
    SEP    (data_at shr (tarray tuint 14) (* r contanis the representation of A mod p *)
   (*cont*)(map Vint (map Int.repr (int_to_list ((list_to_int contents_a) mod prime)))) r ;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a).

Definition curve448Red_INV_1    (a : val)  (contents_a : list Z) 
                                (b : val) (contents_b : list val) (shb : share)
                                (h : Z) (gv : globals) 
:= 
    (EX i : Z,
    (PROP   (Zlength contents_a = 14;
            writable_share shb)
    LOCAL   (temp _temp (Vlong (Int64.repr (Int.signed (Int.repr 1))));
            lvar _b (tarray tuint 14) b; gvars gv; 
            temp _a a; temp _h (Vint (Int.repr h)))
    SEP     (data_at shb (tarray tuint 14) 
            (map Vint (map Int.repr contents_a)) a
            )))%assert.
                
Definition Gprog : funspecs := ltac:(with_library prog [ curve448Red_spec ]).

Lemma body_curve448Red : semax_body Vprog Gprog f_curve448Red curve448Red_spec.
Proof.
    start_function.
    forward.
    forward.
    forward_for_simple_bound 7 
        (curve448Red_INV_1 a contents_a v_b contents_b shb h gv).  




