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

Compute prime. 

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

Definition curve448Red_INV_1    (r : val)  shr (contents_r : list val) 
                                (a : val)  (contents_a : list Z) (h : Z) 
                                (t : val)  
                                (b : )
:= 
    (EX i : Z,
    (PROP   (writable_share shr; 
            Zlength contents_r = 14;
            Zlength contents_a = 14)
    LOCAL   (temp _r r ; temp _temp t ; temp _b b)
    SEP     (data_at shr (tarray tuint 14) 
            (map Vint (map Int.repr contents_a)) a
            )))%assert.
                


