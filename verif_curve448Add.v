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


Definition prime: Z := 2^448 - 2^224 - 1.

Definition undef14 :=
       [Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef;
        Vundef; Vundef; Vundef; Vundef; Vundef; Vundef; Vundef].

Lemma L3 (z : Z) : 
0 <= z < Int64.modulus -> Int64.unsigned (Int64.repr z) = z.
Proof.
   intros.
   rewrite Int64.unsigned_repr_eq.
   rewrite Z.mod_small; auto.
Qed.

Lemma  L4' (z : Z): 
Int.eq (Int.repr z) Int.mone = false -> z mod Int.modulus ≠ Int.modulus - 1.
Proof.
   intros.
   apply int_eq_false_e in H.
   unfold "≠".
   intros.
   replace (Int.modulus - 1) with (Int.modulus - 1 mod Int.modulus) in H0.
   assert (Int.repr z = Int.repr (Int.modulus - 1)).
   apply modulo_samerepr.
   apply H0.
   replace (Int.repr (Int.modulus - 1)) with (Int.repr (- 1)) in H1.
   contradiction.
   rewrite modulo_samerepr with (y:= Int.modulus - 1); reflexivity.
   apply Zmod_small with (a := Int.modulus - 1) (n:= Int.modulus).
   easy.
Qed.

Lemma L4 (z : Z) :
Int.eq (Int.repr z) Int.mone = false -> z mod Int.modulus < Int.modulus - 1.
Proof.
   intros. 
   apply int_eq_false_e in H.
   unfold Int.mone in H.
   apply Znot_ge_lt.
   unfold not.
   intros.
   assert (Int.modulus ≠ 0) by easy.
   apply Z.mod_bound_or with (a := z) in H1.
   destruct H1.
   destruct H1.
   assert (z mod Int.modulus <= Int.modulus - 1).
   apply Zlt_succ_le.
   replace (Z.succ (Int.modulus - 1)) with (Int.modulus) by easy.
   assumption.
   assert ( z mod Int.modulus = Int.modulus - 1). 
   apply Z.ge_le in H0.
   apply Z.le_antisymm; assumption.
   replace (Int.modulus - 1) with (- 1 mod Int.modulus) in H4 by easy.
   apply modulo_samerepr in H4.
   contradiction.
   destruct H1.
   assert (Int.modulus < 0).
   apply Z.lt_le_trans with (m:= z mod Int.modulus); assumption.
   discriminate H3. 
   Qed.

Lemma int64_shru_small (z : Z) : 0 <= z < two_p 32 ->
   Int64.shru (Int64.repr z) (Int64.repr 32) = Int64.zero.
Proof.
   intros.
   rewrite Int64.shru_div_two_p. 
   assert (Int64.unsigned (Int64.repr z) / two_p (Int64.unsigned (Int64.repr 32)) = 0).
   rewrite Zdiv_small; try easy.
   split.
   destruct H.
   rewrite L3; try easy.
   split; try easy.
   assert ((two_p 32) < Int64.modulus) by easy.
   apply Z.lt_trans with (two_p 32); assumption.
   replace (Int64.unsigned (Int64.repr 32)) with 32 by easy.
   destruct H.
   rewrite L3; try easy.
   split; try easy.
   assert ((two_p 32) < Int64.modulus) by easy.
   apply Z.lt_trans with (two_p 32); assumption.
   rewrite H0. easy.
Qed. 

Lemma div_eucl_by_hand: forall a b q r: Z,
0 < b -> 
0 <= r < b -> 
a = q * b + r -> 
Z.div_eucl a b = (q, r).
Proof.
    intros.
    rewrite Zaux.Zdiv_eucl_unique.
    (* Search (_ -> _ / _ = _). *)
    rewrite H1 at 1.
    rewrite Z.div_add_l; try lia.
    rewrite Z.div_small; try lia.
    rewrite H1.
    rewrite Z.add_mod; try lia.
    rewrite Z.mod_mul; try lia.
    (* assert ((0 + r mod b) mod b = r). *)
    replace (0 + r mod b) with (r mod b) by lia.
    rewrite Z.mod_mod; try lia.
    rewrite Z.mod_small; try lia.
    replace (q + 0) with (q) by lia.
    reflexivity.
Qed.

Lemma  div_bound_double: forall n z : Z,
0 < n -> 
n <= z < 2 * n -> 
z / n = 1.
Proof.
    intros.
    unfold "/".
    assert (Z.div_eucl z (n) = (1, z-n)). 
    assert (z = n + (z - n)) by lia.
    rewrite div_eucl_by_hand with (q:= 1) (r:= z - n); try lia.
    reflexivity.
    rewrite H1.
    reflexivity.
Qed.

Lemma int64_shru_big (z : Z) : two_p 32 <= z < two_p 33 ->
   Int64.shru (Int64.repr z) (Int64.repr 32) = Int64.one.
Proof.
    intros.
    rewrite Int64.shru_div_two_p.
    replace (Int64.unsigned (Int64.repr 32)) with 32 by easy. 
    rewrite L3.
    assert (z / two_p 32 = 1).
    apply div_bound_double; try easy.
    rewrite H0; easy.
    destruct H.
    split.
    assert (0 <= two_p 32) by easy.
    lia.  
    assert (two_p 33 < Int64.modulus) by easy.
    lia.
Qed. 

(* %%%%%%%%%%%%%%%%%%%%%%%%% *)
Definition curve448Add_spec : ident * funspec :=
DECLARE _curve448Add
WITH    r : val,
        shr : share,
        a : val,
        contents_a : list Z,
        b : val,
        contents_b : list Z,
        gv : globals
PRE [ tptr tuint, tptr tuint, tptr tuint ]
    PROP   (writable_share shr;
            Zlength contents_a = 14;
            Zlength contents_b = 14;
            0 <= (list_to_int contents_a) < prime;
            0 <= (list_to_int contents_b) < prime;
            forall x : Z, In x contents_a → 0 <= x < 2 ^ 32 /\ x mod Int.modulus < 2^32;
            forall x : Z, In x contents_b → 0 <= x < 2 ^ 32 /\ x mod Int.modulus < 2^32)
    PARAMS (r ; a ; b) GLOBALS (gv)
    SEP    (data_at_ shr (tarray tuint 14) r;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_b)) b)
POST [ tvoid ]
    PROP   ()
    RETURN ()
    SEP    (data_at shr (tarray tuint 14) (* r contains the representation of A + B mod p *)
   (*cont*)(map Vint (map Int.repr (int_to_list (((list_to_int contents_a) + (list_to_int contents_b)) mod prime)))) r ;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a ;
            data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_b)) b).

Definition carrying (i : Z) (a b : list Z) : bool:=
        if (i =? 0) then false
        else ((Znth i a) + (Znth i b)) >=? 2^32.

Definition curve448Add_INV  (a : val)  (contents_a : list Z)
                            (b : val)  (contents_b : list Z)
                            (r : val) (shr : share) (gv : globals) :=
    (EX i : Z, EX t : int64,
    (PROP   (Zlength contents_a = 14; Zlength contents_b = 14;
             t = Int64.zero \/ t = Int64.one)
    LOCAL   (temp _a a; temp _b b; temp _r r;
            temp _temp (Vlong t);
            gvars gv)
    SEP     (  data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_a)) a;
               data_at Tsh (tarray tuint 14) (map Vint (map Int.repr contents_b)) b;
               data_at shr (tarray tuint 14)
               ((sublist.sublist 0 i (map Vint (map Int.repr
                     (int_to_list ((list_to_int contents_a + list_to_int contents_b) mod prime)))))
               ++ sublist.sublist i 14 undef14) r
            )))%assert.

Definition Gprog : funspecs := ltac:(with_library prog [ curve448Add_spec ]).

Lemma body_curve448Red : semax_body Vprog Gprog f_curve448Add curve448Add_spec.
Proof.
    start_function.
    forward.
    forward_for_simple_bound 14
    (curve448Add_INV a contents_a b contents_b r shr gv).
    Exists (Int64.repr 0). 
    entailer!.
    easy.
    repeat forward.
    entailer!.
    Exists ((Int64.shru
    (Int64.add
       (Int64.add t
          (Int64.repr
             (Int.unsigned
                (Int.repr (Znth i contents_a)))))
       (Int64.repr
          (Int.unsigned (Int.repr (Znth i contents_b)))))
    (Int64.repr (Int.unsigned (Int.repr 32))))).
    entailer!.
    destruct H6; rewrite H6. 
    rewrite Int64.add_zero_l.
    autorewrite with norm.
    assert (sum: ((((Int.unsigned (Int.repr (Znth i contents_a)) 
                    + Int.unsigned (Int.repr (Znth i contents_b)))) < 2^32) 
            \/ 2^32 <= ((Int.unsigned (Int.repr (Znth i contents_a)) 
                    + Int.unsigned (Int.repr (Znth i contents_b)))))) by lia.
    destruct sum as [sum_lt | sum_ge].
    left.
    rewrite int64_shru_small; try easy.
    split.
    apply Z.add_nonneg_nonneg; apply Int64.int_unsigned_range.
    replace (two_p 32) with (2^32) by easy; assumption.
    right.
    apply int64_shru_big.
    split.
    replace (two_p 32) with (2^32) by easy; assumption.
    assert (Int.unsigned (Int.repr (Znth i contents_a)) < 2^32).
    rewrite Int.unsigned_repr_eq.
    apply H3.
    apply Znth_In; lia.
    assert (Int.unsigned (Int.repr (Znth i contents_b)) < 2^32).
    rewrite Int.unsigned_repr_eq.
    apply H4.
    apply Znth_In; lia.
    replace (two_p 33) with (2^32 + 2^32) by easy.
    apply Z.add_lt_mono; assumption. 
    (* Case where t = 1. *)
    rewrite Int64.add_assoc.
    autorewrite with norm.
    unfold Int64.add.
    rewrite Int64.unsigned_one.
    autorewrite with norm. 
    assert (sum: ((((1 + Int.unsigned (Int.repr (Znth i contents_a)) 
                    + Int.unsigned (Int.repr (Znth i contents_b)))) < 2^32 ) 
            \/ 2^32 <= ((1 + Int.unsigned (Int.repr (Znth i contents_a)) 
                    + Int.unsigned (Int.repr (Znth i contents_b)))))) by lia.
    destruct sum as [sum_lt | sum_ge].
    left.
    rewrite int64_shru_small; try easy.
    split.
    apply Z.add_nonneg_nonneg; try easy.
    apply Z.add_nonneg_nonneg; apply Int64.int_unsigned_range.
    replace (two_p 32) with (2^32) by easy; lia.
    right.
    rewrite int64_shru_big; try easy.
    split.
    replace (two_p 32) with (2^32) by easy; lia.
    assert (Int.unsigned (Int.repr (Znth i contents_a)) < 2^32).
    rewrite Int.unsigned_repr_eq.
    apply H3.
    apply Znth_In; lia.
    assert (Int.unsigned (Int.repr (Znth i contents_b)) < 2^32).
    rewrite Int.unsigned_repr_eq.
    apply H4.
    apply Znth_In; lia.
    replace (two_p 33) with (2^32 + 2^32) by easy.
    rewrite Z.add_assoc.
    apply Z.add_le_lt_mono; lia.
    assert (data_at_r : (upd_Znth i
     (sublist.sublist 0 i 
     (map Vint (map Int.repr (int_to_list ((list_to_int contents_a + list_to_int contents_b) mod prime)))) ++
      sublist.sublist i 14 undef14)
     (Vint
        (Int.repr
           (Int64.unsigned
              (Int64.and
                 (Int64.add (Int64.add t (Int64.repr (Int.unsigned (Int.repr (Znth i contents_a)))))
                    (Int64.repr (Int.unsigned (Int.repr (Znth i contents_b)))))
                 (Int64.repr (Int.unsigned (Int.repr (-1))))))))) =
      (sublist.sublist 0 (i + 1)
         (map Vint
            (map Int.repr (int_to_list ((list_to_int contents_a + list_to_int contents_b) mod prime)))) ++
       sublist.sublist (i + 1) 14 undef14) ).


    rewrite <- !(sublist_rejoin 0 i (i+1)); try easy.
    rewrite <- app_assoc.   
    rewrite upd_list_app_upper.
    rewrite Zlength_sublist; try easy.
    autorewrite with sublist.  
    rewrite sublist_update_0th_gen; try easy; try lia.
    rewrite sublist_len_1.
    repeat f_equal.

    rewrite Znth_map_Vint_map_Int_repr.
    replace (i) with (Z.of_nat (Z.to_nat i)) by lia.
    rewrite Znth_int_to_list.
    f_equal.
    replace (Z.of_nat (Z.to_nat i)) with i by lia. 
    autorewrite with sublist in *|-.
    About Vlong.
    assert ((Znth i contents_a = -1) \/ (Znth i contents_a <> -1)).
    lia.
    destruct H10; try rewrite H10.
    replace ((Int64.add Int64.one (Int64.repr (Int.unsigned (Int.repr (-1)))))) 
    with (Int64.repr(2^32)) by easy.
    replace ((Int64.and (Int64.repr (2 ^ 32))
    (Int64.repr (Int.unsigned (Int.repr (-1)))))) with (Int64.zero) by easy.
    replace (Int.repr (Int64.unsigned Int64.zero)) with (Int.repr 0) by easy.
    simpl.
admit.

rewrite data_at_r; easy.

Intros t.

(* Need Red. *)





    
    


(* void curve448Add(uint32_t *r, const uint32_t *a, const uint32_t *b)
{
   uint_t i;
   uint64_t temp;

   //Compute R = A + B
   temp = 0;
   for(i = 0; i < 14; i++)
   {
      temp += a[i];
      temp += b[i];
      r[i] = temp & 0xFFFFFFFF;
      temp >>= 32;
   }

   //Perform modular reduction
   curve448Red(r, r, (uint32_t) temp);
} *)