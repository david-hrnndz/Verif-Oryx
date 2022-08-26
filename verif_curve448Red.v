Require Import VST.floyd.proofauto.
Require Import curve448.
Require Import list_int_functions.
Require Import stdpp.list.
Require Import ZArith.
Require Import compcert.lib.Coqlib.
Require Import list_lemmas.

Instance CompSpecs : compspecs. Proof. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Local Open Scope Z.

(* curve448Red specification 
   for proof see verif_curve448Red_proofattempt.v *)


Definition prime: Z := 2^448 - 2^224 - 1.
 
Definition undef14 := 
       [Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; 
        Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef].

Definition curve448Red_spec : ident * funspec :=
DECLARE _curve448Red
WITH    r : val,
        shr : share,
        a : val,
        contents_a : list Z,
        h : Z, (* may need writable share *)
        gv : globals
PRE [ tptr tuint, tptr tuint, tuint ]
    PROP   (writable_share shr;
            Zlength contents_a = 14;
            0 <= (list_to_int contents_a) < (2 * prime)
            (*TODO  * @param[in] h The highest term of A*))
    PARAMS (r ; a ; Vint(Int.repr h)) GLOBALS (gv)
    SEP    (data_at_ shr (tarray tuint 14) r;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a)
POST [ tvoid ]
    PROP   ()
    RETURN ()                               
    SEP    (data_at shr (tarray tuint 14) (* r contains the representation of A mod p *)
   (*cont*)(map Vint (map Int.repr (int_to_list ((list_to_int contents_a) mod prime)))) r ;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a).


Fixpoint allprev_mone_aux (n : nat) (a : list Z) : bool :=
   match n with 
   | O   => true
   | S n' => (Int.eq (Int.repr (Znth (Z.of_nat n') a)) Int.mone) 
            && allprev_mone_aux n' a
   end.
   
Definition allprev_mone (i : Z) (a : list Z) := allprev_mone_aux (Z.to_nat i) a.

Definition curve448Red_INV_1    (a : val)  (contents_a : list Z) 
                     (b : val)  (r : val) (shr : share)
                     (h : Z) (gv : globals) := 
    (EX i : Z,
    (PROP   (Zlength contents_a = 14)
    LOCAL   (temp _temp (if allprev_mone i contents_a 
               then Vlong Int64.one else Vlong Int64.zero);
            lvar _b (tarray tuint 14) b; 
            gvars gv; 
            temp _a a; temp _h (Vint (Int.repr h)))
    SEP     ( 
                data_at_ shr (tarray tuint 14) r;
                data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a; 
                data_at Tsh (tarray tuint 14)  
                ((sublist.sublist 0 i (map Vint (map Int.repr (int_to_list ((list_to_int contents_a) - prime)))))
                ++ sublist.sublist i 14 undef14) b
            )))%assert.

Definition Gprog : funspecs := ltac:(with_library prog [ curve448Red_spec ]).

