From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.9".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "macos".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "curve448.c".
  Definition normalized := true.
End Info.

Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _a : ident := $"a".
Definition _b : ident := $"b".
Definition _c : ident := $"c".
Definition _curve448Add : ident := $"curve448Add".
Definition _curve448AddInt : ident := $"curve448AddInt".
Definition _curve448Comp : ident := $"curve448Comp".
Definition _curve448Copy : ident := $"curve448Copy".
Definition _curve448Inv : ident := $"curve448Inv".
Definition _curve448Mul : ident := $"curve448Mul".
Definition _curve448MulInt : ident := $"curve448MulInt".
Definition _curve448Pwr2 : ident := $"curve448Pwr2".
Definition _curve448Red : ident := $"curve448Red".
Definition _curve448Select : ident := $"curve448Select".
Definition _curve448SetInt : ident := $"curve448SetInt".
Definition _curve448Sqr : ident := $"curve448Sqr".
Definition _curve448Sqrt : ident := $"curve448Sqrt".
Definition _curve448Sub : ident := $"curve448Sub".
Definition _curve448SubInt : ident := $"curve448SubInt".
Definition _curve448Swap : ident := $"curve448Swap".
Definition _dummy : ident := $"dummy".
Definition _h : ident := $"h".
Definition _i : ident := $"i".
Definition _j : ident := $"j".
Definition _main : ident := $"main".
Definition _mask : ident := $"mask".
Definition _n : ident := $"n".
Definition _r : ident := $"r".
Definition _res : ident := $"res".
Definition _temp : ident := $"temp".
Definition _u : ident := $"u".
Definition _v : ident := $"v".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_curve448SetInt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tuint)) :: (_b, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Etempvar _a (tptr tuint)) (Econst_int (Int.repr 0) tint)
        (tptr tuint)) tuint) (Etempvar _b tuint))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 1) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                       (Econst_int (Int.repr 14) tint) tint)
          Sskip
          Sbreak)
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _a (tptr tuint)) (Etempvar _i tuint)
              (tptr tuint)) tuint) (Econst_int (Int.repr 0) tint)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint)))))
|}.

Definition f_curve448Add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuint)) :: (_a, (tptr tuint)) ::
                (_b, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_temp, tulong) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _temp (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Sset _i (Econst_int (Int.repr 0) tint)))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                       (Econst_int (Int.repr 14) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Etempvar _a (tptr tuint)) (Etempvar _i tuint)
                  (tptr tuint)) tuint))
            (Sset _temp
              (Ebinop Oadd (Etempvar _temp tulong) (Etempvar _t'2 tuint)
                tulong)))
          (Ssequence
            (Ssequence
              (Sset _t'1
                (Ederef
                  (Ebinop Oadd (Etempvar _b (tptr tuint)) (Etempvar _i tuint)
                    (tptr tuint)) tuint))
              (Sset _temp
                (Ebinop Oadd (Etempvar _temp tulong) (Etempvar _t'1 tuint)
                  tulong)))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _r (tptr tuint)) (Etempvar _i tuint)
                    (tptr tuint)) tuint)
                (Ebinop Oand (Etempvar _temp tulong)
                  (Econst_int (Int.repr (-1)) tuint) tulong))
              (Sset _temp
                (Ebinop Oshr (Etempvar _temp tulong)
                  (Econst_int (Int.repr 32) tint) tulong))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint))))
  (Scall None
    (Evar _curve448Red (Tfunction
                         (Tcons (tptr tuint)
                           (Tcons (tptr tuint) (Tcons tuint Tnil))) tvoid
                         cc_default))
    ((Etempvar _r (tptr tuint)) :: (Etempvar _r (tptr tuint)) ::
     (Ecast (Etempvar _temp tulong) tuint) :: nil)))
|}.

Definition f_curve448AddInt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuint)) :: (_a, (tptr tuint)) :: (_b, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_temp, tulong) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _temp (Ecast (Etempvar _b tuint) tulong))
      (Sset _i (Econst_int (Int.repr 0) tint)))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                       (Econst_int (Int.repr 14) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd (Etempvar _a (tptr tuint)) (Etempvar _i tuint)
                  (tptr tuint)) tuint))
            (Sset _temp
              (Ebinop Oadd (Etempvar _temp tulong) (Etempvar _t'1 tuint)
                tulong)))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _r (tptr tuint)) (Etempvar _i tuint)
                  (tptr tuint)) tuint)
              (Ebinop Oand (Etempvar _temp tulong)
                (Econst_int (Int.repr (-1)) tuint) tulong))
            (Sset _temp
              (Ebinop Oshr (Etempvar _temp tulong)
                (Econst_int (Int.repr 32) tint) tulong)))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint))))
  (Scall None
    (Evar _curve448Red (Tfunction
                         (Tcons (tptr tuint)
                           (Tcons (tptr tuint) (Tcons tuint Tnil))) tvoid
                         cc_default))
    ((Etempvar _r (tptr tuint)) :: (Etempvar _r (tptr tuint)) ::
     (Ecast (Etempvar _temp tulong) tuint) :: nil)))
|}.

Definition f_curve448Sub := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuint)) :: (_a, (tptr tuint)) ::
                (_b, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_temp, tlong) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _temp
        (Ecast (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tlong))
      (Sset _i (Econst_int (Int.repr 0) tint)))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                       (Econst_int (Int.repr 7) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Ederef
                (Ebinop Oadd (Etempvar _a (tptr tuint)) (Etempvar _i tuint)
                  (tptr tuint)) tuint))
            (Sset _temp
              (Ebinop Oadd (Etempvar _temp tlong) (Etempvar _t'4 tuint)
                tlong)))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Ederef
                  (Ebinop Oadd (Etempvar _b (tptr tuint)) (Etempvar _i tuint)
                    (tptr tuint)) tuint))
              (Sset _temp
                (Ebinop Osub (Etempvar _temp tlong) (Etempvar _t'3 tuint)
                  tlong)))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _r (tptr tuint)) (Etempvar _i tuint)
                    (tptr tuint)) tuint)
                (Ebinop Oand (Etempvar _temp tlong)
                  (Econst_int (Int.repr (-1)) tuint) tlong))
              (Sset _temp
                (Ebinop Oshr (Etempvar _temp tlong)
                  (Econst_int (Int.repr 32) tint) tlong))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _temp
          (Ebinop Osub (Etempvar _temp tlong) (Econst_int (Int.repr 1) tint)
            tlong))
        (Sset _i (Econst_int (Int.repr 7) tint)))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                         (Econst_int (Int.repr 14) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Etempvar _a (tptr tuint)) (Etempvar _i tuint)
                    (tptr tuint)) tuint))
              (Sset _temp
                (Ebinop Oadd (Etempvar _temp tlong) (Etempvar _t'2 tuint)
                  tlong)))
            (Ssequence
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd (Etempvar _b (tptr tuint))
                      (Etempvar _i tuint) (tptr tuint)) tuint))
                (Sset _temp
                  (Ebinop Osub (Etempvar _temp tlong) (Etempvar _t'1 tuint)
                    tlong)))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _r (tptr tuint))
                      (Etempvar _i tuint) (tptr tuint)) tuint)
                  (Ebinop Oand (Etempvar _temp tlong)
                    (Econst_int (Int.repr (-1)) tuint) tlong))
                (Sset _temp
                  (Ebinop Oshr (Etempvar _temp tlong)
                    (Econst_int (Int.repr 32) tint) tlong))))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Ssequence
      (Sset _temp
        (Ebinop Oadd (Etempvar _temp tlong) (Econst_int (Int.repr 1) tint)
          tlong))
      (Scall None
        (Evar _curve448Red (Tfunction
                             (Tcons (tptr tuint)
                               (Tcons (tptr tuint) (Tcons tuint Tnil))) tvoid
                             cc_default))
        ((Etempvar _r (tptr tuint)) :: (Etempvar _r (tptr tuint)) ::
         (Ecast (Etempvar _temp tlong) tuint) :: nil)))))
|}.

Definition f_curve448SubInt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuint)) :: (_a, (tptr tuint)) :: (_b, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_temp, tlong) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _temp (Ecast (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tlong))
  (Ssequence
    (Sset _temp
      (Ebinop Osub (Etempvar _temp tlong) (Etempvar _b tuint) tlong))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                           (Econst_int (Int.repr 7) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Sset _t'2
                  (Ederef
                    (Ebinop Oadd (Etempvar _a (tptr tuint))
                      (Etempvar _i tuint) (tptr tuint)) tuint))
                (Sset _temp
                  (Ebinop Oadd (Etempvar _temp tlong) (Etempvar _t'2 tuint)
                    tlong)))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Etempvar _r (tptr tuint))
                      (Etempvar _i tuint) (tptr tuint)) tuint)
                  (Ebinop Oand (Etempvar _temp tlong)
                    (Econst_int (Int.repr (-1)) tuint) tlong))
                (Sset _temp
                  (Ebinop Oshr (Etempvar _temp tlong)
                    (Econst_int (Int.repr 32) tint) tlong)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint))))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _temp
              (Ebinop Osub (Etempvar _temp tlong)
                (Econst_int (Int.repr 1) tint) tlong))
            (Sset _i (Econst_int (Int.repr 7) tint)))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                             (Econst_int (Int.repr 14) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Sset _t'1
                    (Ederef
                      (Ebinop Oadd (Etempvar _a (tptr tuint))
                        (Etempvar _i tuint) (tptr tuint)) tuint))
                  (Sset _temp
                    (Ebinop Oadd (Etempvar _temp tlong) (Etempvar _t'1 tuint)
                      tlong)))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Etempvar _r (tptr tuint))
                        (Etempvar _i tuint) (tptr tuint)) tuint)
                    (Ebinop Oand (Etempvar _temp tlong)
                      (Econst_int (Int.repr (-1)) tuint) tlong))
                  (Sset _temp
                    (Ebinop Oshr (Etempvar _temp tlong)
                      (Econst_int (Int.repr 32) tint) tlong)))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
                tuint))))
        (Ssequence
          (Sset _temp
            (Ebinop Oadd (Etempvar _temp tlong)
              (Econst_int (Int.repr 1) tint) tlong))
          (Scall None
            (Evar _curve448Red (Tfunction
                                 (Tcons (tptr tuint)
                                   (Tcons (tptr tuint) (Tcons tuint Tnil)))
                                 tvoid cc_default))
            ((Etempvar _r (tptr tuint)) :: (Etempvar _r (tptr tuint)) ::
             (Ecast (Etempvar _temp tlong) tuint) :: nil)))))))
|}.

Definition f_curve448Mul := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuint)) :: (_a, (tptr tuint)) ::
                (_b, (tptr tuint)) :: nil);
  fn_vars := ((_u, (tarray tuint 28)) :: nil);
  fn_temps := ((_i, tuint) :: (_j, tuint) :: (_c, tulong) ::
               (_temp, tulong) :: (_t'13, tuint) :: (_t'12, tuint) ::
               (_t'11, tuint) :: (_t'10, tuint) :: (_t'9, tuint) ::
               (_t'8, tuint) :: (_t'7, tuint) :: (_t'6, tuint) ::
               (_t'5, tuint) :: (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _temp (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Sset _c (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                           (Econst_int (Int.repr 28) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                             (Econst_int (Int.repr 14) tint) tint)
                (Ssequence
                  (Sset _j (Econst_int (Int.repr 0) tint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Ole (Etempvar _j tuint)
                                     (Etempvar _i tuint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Ssequence
                          (Sset _t'12
                            (Ederef
                              (Ebinop Oadd (Etempvar _a (tptr tuint))
                                (Etempvar _j tuint) (tptr tuint)) tuint))
                          (Ssequence
                            (Sset _t'13
                              (Ederef
                                (Ebinop Oadd (Etempvar _b (tptr tuint))
                                  (Ebinop Osub (Etempvar _i tuint)
                                    (Etempvar _j tuint) tuint) (tptr tuint))
                                tuint))
                            (Sset _temp
                              (Ebinop Oadd (Etempvar _temp tulong)
                                (Ebinop Omul
                                  (Ecast (Etempvar _t'12 tuint) tulong)
                                  (Etempvar _t'13 tuint) tulong) tulong))))
                        (Ssequence
                          (Sset _c
                            (Ebinop Oadd (Etempvar _c tulong)
                              (Ebinop Oshr (Etempvar _temp tulong)
                                (Econst_int (Int.repr 32) tint) tulong)
                              tulong))
                          (Sset _temp
                            (Ebinop Oand (Etempvar _temp tulong)
                              (Econst_int (Int.repr (-1)) tuint) tulong)))))
                    (Sset _j
                      (Ebinop Oadd (Etempvar _j tuint)
                        (Econst_int (Int.repr 1) tint) tuint))))
                (Ssequence
                  (Sset _j
                    (Ebinop Osub (Etempvar _i tuint)
                      (Econst_int (Int.repr 13) tint) tuint))
                  (Sloop
                    (Ssequence
                      (Sifthenelse (Ebinop Olt (Etempvar _j tuint)
                                     (Econst_int (Int.repr 14) tint) tint)
                        Sskip
                        Sbreak)
                      (Ssequence
                        (Ssequence
                          (Sset _t'10
                            (Ederef
                              (Ebinop Oadd (Etempvar _a (tptr tuint))
                                (Etempvar _j tuint) (tptr tuint)) tuint))
                          (Ssequence
                            (Sset _t'11
                              (Ederef
                                (Ebinop Oadd (Etempvar _b (tptr tuint))
                                  (Ebinop Osub (Etempvar _i tuint)
                                    (Etempvar _j tuint) tuint) (tptr tuint))
                                tuint))
                            (Sset _temp
                              (Ebinop Oadd (Etempvar _temp tulong)
                                (Ebinop Omul
                                  (Ecast (Etempvar _t'10 tuint) tulong)
                                  (Etempvar _t'11 tuint) tulong) tulong))))
                        (Ssequence
                          (Sset _c
                            (Ebinop Oadd (Etempvar _c tulong)
                              (Ebinop Oshr (Etempvar _temp tulong)
                                (Econst_int (Int.repr 32) tint) tulong)
                              tulong))
                          (Sset _temp
                            (Ebinop Oand (Etempvar _temp tulong)
                              (Econst_int (Int.repr (-1)) tuint) tulong)))))
                    (Sset _j
                      (Ebinop Oadd (Etempvar _j tuint)
                        (Econst_int (Int.repr 1) tint) tuint)))))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _u (tarray tuint 28))
                      (Etempvar _i tuint) (tptr tuint)) tuint)
                  (Ebinop Oand (Etempvar _temp tulong)
                    (Econst_int (Int.repr (-1)) tuint) tulong))
                (Ssequence
                  (Sset _temp
                    (Ebinop Oand (Etempvar _c tulong)
                      (Econst_int (Int.repr (-1)) tuint) tulong))
                  (Sset _c
                    (Ebinop Oshr (Etempvar _c tulong)
                      (Econst_int (Int.repr 32) tint) tulong))))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
              tuint))))
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _temp (Ecast (Econst_int (Int.repr 0) tint) tulong))
            (Sset _i (Econst_int (Int.repr 0) tint)))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                             (Econst_int (Int.repr 7) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Ssequence
                  (Sset _t'9
                    (Ederef
                      (Ebinop Oadd (Evar _u (tarray tuint 28))
                        (Etempvar _i tuint) (tptr tuint)) tuint))
                  (Sset _temp
                    (Ebinop Oadd (Etempvar _temp tulong)
                      (Etempvar _t'9 tuint) tulong)))
                (Ssequence
                  (Ssequence
                    (Sset _t'8
                      (Ederef
                        (Ebinop Oadd (Evar _u (tarray tuint 28))
                          (Ebinop Oadd (Etempvar _i tuint)
                            (Econst_int (Int.repr 14) tint) tuint)
                          (tptr tuint)) tuint))
                    (Sset _temp
                      (Ebinop Oadd (Etempvar _temp tulong)
                        (Etempvar _t'8 tuint) tulong)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'7
                        (Ederef
                          (Ebinop Oadd (Evar _u (tarray tuint 28))
                            (Ebinop Oadd (Etempvar _i tuint)
                              (Econst_int (Int.repr 21) tint) tuint)
                            (tptr tuint)) tuint))
                      (Sset _temp
                        (Ebinop Oadd (Etempvar _temp tulong)
                          (Etempvar _t'7 tuint) tulong)))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _u (tarray tuint 28))
                            (Etempvar _i tuint) (tptr tuint)) tuint)
                        (Ebinop Oand (Etempvar _temp tulong)
                          (Econst_int (Int.repr (-1)) tuint) tulong))
                      (Sset _temp
                        (Ebinop Oshr (Etempvar _temp tulong)
                          (Econst_int (Int.repr 32) tint) tulong)))))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
                tuint))))
        (Ssequence
          (Ssequence
            (Sset _i (Econst_int (Int.repr 7) tint))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                               (Econst_int (Int.repr 14) tint) tint)
                  Sskip
                  Sbreak)
                (Ssequence
                  (Ssequence
                    (Sset _t'6
                      (Ederef
                        (Ebinop Oadd (Evar _u (tarray tuint 28))
                          (Etempvar _i tuint) (tptr tuint)) tuint))
                    (Sset _temp
                      (Ebinop Oadd (Etempvar _temp tulong)
                        (Etempvar _t'6 tuint) tulong)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'5
                        (Ederef
                          (Ebinop Oadd (Evar _u (tarray tuint 28))
                            (Ebinop Oadd (Etempvar _i tuint)
                              (Econst_int (Int.repr 7) tint) tuint)
                            (tptr tuint)) tuint))
                      (Sset _temp
                        (Ebinop Oadd (Etempvar _temp tulong)
                          (Etempvar _t'5 tuint) tulong)))
                    (Ssequence
                      (Ssequence
                        (Sset _t'4
                          (Ederef
                            (Ebinop Oadd (Evar _u (tarray tuint 28))
                              (Ebinop Oadd (Etempvar _i tuint)
                                (Econst_int (Int.repr 14) tint) tuint)
                              (tptr tuint)) tuint))
                        (Sset _temp
                          (Ebinop Oadd (Etempvar _temp tulong)
                            (Etempvar _t'4 tuint) tulong)))
                      (Ssequence
                        (Ssequence
                          (Sset _t'3
                            (Ederef
                              (Ebinop Oadd (Evar _u (tarray tuint 28))
                                (Ebinop Oadd (Etempvar _i tuint)
                                  (Econst_int (Int.repr 14) tint) tuint)
                                (tptr tuint)) tuint))
                          (Sset _temp
                            (Ebinop Oadd (Etempvar _temp tulong)
                              (Etempvar _t'3 tuint) tulong)))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _u (tarray tuint 28))
                                (Etempvar _i tuint) (tptr tuint)) tuint)
                            (Ebinop Oand (Etempvar _temp tulong)
                              (Econst_int (Int.repr (-1)) tuint) tulong))
                          (Sset _temp
                            (Ebinop Oshr (Etempvar _temp tulong)
                              (Econst_int (Int.repr 32) tint) tulong))))))))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tuint)
                  (Econst_int (Int.repr 1) tint) tuint))))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _c (Etempvar _temp tulong))
                (Sset _i (Econst_int (Int.repr 0) tint)))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                 (Econst_int (Int.repr 7) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Ssequence
                      (Sset _t'2
                        (Ederef
                          (Ebinop Oadd (Evar _u (tarray tuint 28))
                            (Etempvar _i tuint) (tptr tuint)) tuint))
                      (Sset _temp
                        (Ebinop Oadd (Etempvar _temp tulong)
                          (Etempvar _t'2 tuint) tulong)))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _u (tarray tuint 28))
                            (Etempvar _i tuint) (tptr tuint)) tuint)
                        (Ebinop Oand (Etempvar _temp tulong)
                          (Econst_int (Int.repr (-1)) tuint) tulong))
                      (Sset _temp
                        (Ebinop Oshr (Etempvar _temp tulong)
                          (Econst_int (Int.repr 32) tint) tulong)))))
                (Sset _i
                  (Ebinop Oadd (Etempvar _i tuint)
                    (Econst_int (Int.repr 1) tint) tuint))))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _temp
                    (Ebinop Oadd (Etempvar _temp tulong) (Etempvar _c tulong)
                      tulong))
                  (Sset _i (Econst_int (Int.repr 7) tint)))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                                   (Econst_int (Int.repr 14) tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Ssequence
                        (Sset _t'1
                          (Ederef
                            (Ebinop Oadd (Evar _u (tarray tuint 28))
                              (Etempvar _i tuint) (tptr tuint)) tuint))
                        (Sset _temp
                          (Ebinop Oadd (Etempvar _temp tulong)
                            (Etempvar _t'1 tuint) tulong)))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _u (tarray tuint 28))
                              (Etempvar _i tuint) (tptr tuint)) tuint)
                          (Ebinop Oand (Etempvar _temp tulong)
                            (Econst_int (Int.repr (-1)) tuint) tulong))
                        (Sset _temp
                          (Ebinop Oshr (Etempvar _temp tulong)
                            (Econst_int (Int.repr 32) tint) tulong)))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tuint)
                      (Econst_int (Int.repr 1) tint) tuint))))
              (Scall None
                (Evar _curve448Red (Tfunction
                                     (Tcons (tptr tuint)
                                       (Tcons (tptr tuint)
                                         (Tcons tuint Tnil))) tvoid
                                     cc_default))
                ((Etempvar _r (tptr tuint)) :: (Evar _u (tarray tuint 28)) ::
                 (Ecast (Etempvar _temp tulong) tuint) :: nil)))))))))
|}.

Definition f_curve448MulInt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuint)) :: (_a, (tptr tuint)) :: (_b, tuint) ::
                nil);
  fn_vars := ((_u, (tarray tuint 14)) :: nil);
  fn_temps := ((_i, tint) :: (_c, tulong) :: (_temp, tulong) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _temp (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Sset _i (Econst_int (Int.repr 0) tint)))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 14) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Ederef
                (Ebinop Oadd (Etempvar _a (tptr tuint)) (Etempvar _i tint)
                  (tptr tuint)) tuint))
            (Sset _temp
              (Ebinop Oadd (Etempvar _temp tulong)
                (Ebinop Omul (Ecast (Etempvar _t'3 tuint) tulong)
                  (Etempvar _b tuint) tulong) tulong)))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _u (tarray tuint 14)) (Etempvar _i tint)
                  (tptr tuint)) tuint)
              (Ebinop Oand (Etempvar _temp tulong)
                (Econst_int (Int.repr (-1)) tuint) tulong))
            (Sset _temp
              (Ebinop Oshr (Etempvar _temp tulong)
                (Econst_int (Int.repr 32) tint) tulong)))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _c (Etempvar _temp tulong))
        (Sset _i (Econst_int (Int.repr 0) tint)))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Econst_int (Int.repr 7) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Evar _u (tarray tuint 14)) (Etempvar _i tint)
                    (tptr tuint)) tuint))
              (Sset _temp
                (Ebinop Oadd (Etempvar _temp tulong) (Etempvar _t'2 tuint)
                  tulong)))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _u (tarray tuint 14)) (Etempvar _i tint)
                    (tptr tuint)) tuint)
                (Ebinop Oand (Etempvar _temp tulong)
                  (Econst_int (Int.repr (-1)) tuint) tulong))
              (Sset _temp
                (Ebinop Oshr (Etempvar _temp tulong)
                  (Econst_int (Int.repr 32) tint) tulong)))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
            tint))))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _temp
            (Ebinop Oadd (Etempvar _temp tulong) (Etempvar _c tulong) tulong))
          (Sset _i (Econst_int (Int.repr 7) tint)))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 14) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd (Evar _u (tarray tuint 14))
                      (Etempvar _i tint) (tptr tuint)) tuint))
                (Sset _temp
                  (Ebinop Oadd (Etempvar _temp tulong) (Etempvar _t'1 tuint)
                    tulong)))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _u (tarray tuint 14))
                      (Etempvar _i tint) (tptr tuint)) tuint)
                  (Ebinop Oand (Etempvar _temp tulong)
                    (Econst_int (Int.repr (-1)) tuint) tulong))
                (Sset _temp
                  (Ebinop Oshr (Etempvar _temp tulong)
                    (Econst_int (Int.repr 32) tint) tulong)))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Scall None
        (Evar _curve448Red (Tfunction
                             (Tcons (tptr tuint)
                               (Tcons (tptr tuint) (Tcons tuint Tnil))) tvoid
                             cc_default))
        ((Etempvar _r (tptr tuint)) :: (Evar _u (tarray tuint 14)) ::
         (Ecast (Etempvar _temp tulong) tuint) :: nil)))))
|}.

Definition f_curve448Sqr := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuint)) :: (_a, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _curve448Mul (Tfunction
                       (Tcons (tptr tuint)
                         (Tcons (tptr tuint) (Tcons (tptr tuint) Tnil)))
                       tvoid cc_default))
  ((Etempvar _r (tptr tuint)) :: (Etempvar _a (tptr tuint)) ::
   (Etempvar _a (tptr tuint)) :: nil))
|}.

Definition f_curve448Pwr2 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuint)) :: (_a, (tptr tuint)) :: (_n, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _curve448Sqr (Tfunction
                         (Tcons (tptr tuint) (Tcons (tptr tuint) Tnil)) tvoid
                         cc_default))
    ((Etempvar _r (tptr tuint)) :: (Etempvar _a (tptr tuint)) :: nil))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 1) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _n tuint)
                       tint)
          Sskip
          Sbreak)
        (Scall None
          (Evar _curve448Sqr (Tfunction
                               (Tcons (tptr tuint) (Tcons (tptr tuint) Tnil))
                               tvoid cc_default))
          ((Etempvar _r (tptr tuint)) :: (Etempvar _r (tptr tuint)) :: nil)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint)))))
|}.

Definition f_curve448Red := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuint)) :: (_a, (tptr tuint)) :: (_h, tuint) ::
                nil);
  fn_vars := ((_b, (tarray tuint 14)) :: nil);
  fn_temps := ((_i, tuint) :: (_temp, tulong) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _temp (Ecast (Econst_int (Int.repr 1) tint) tulong))
      (Sset _i (Econst_int (Int.repr 0) tint)))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                       (Econst_int (Int.repr 7) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Etempvar _a (tptr tuint)) (Etempvar _i tuint)
                  (tptr tuint)) tuint))
            (Sset _temp
              (Ebinop Oadd (Etempvar _temp tulong) (Etempvar _t'2 tuint)
                tulong)))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _b (tarray tuint 14)) (Etempvar _i tuint)
                  (tptr tuint)) tuint)
              (Ebinop Oand (Etempvar _temp tulong)
                (Econst_int (Int.repr (-1)) tuint) tulong))
            (Sset _temp
              (Ebinop Oshr (Etempvar _temp tulong)
                (Econst_int (Int.repr 32) tint) tulong)))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _temp
          (Ebinop Oadd (Etempvar _temp tulong) (Econst_int (Int.repr 1) tint)
            tulong))
        (Sset _i (Econst_int (Int.repr 7) tint)))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                         (Econst_int (Int.repr 14) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Ssequence
              (Sset _t'1
                (Ederef
                  (Ebinop Oadd (Etempvar _a (tptr tuint)) (Etempvar _i tuint)
                    (tptr tuint)) tuint))
              (Sset _temp
                (Ebinop Oadd (Etempvar _temp tulong) (Etempvar _t'1 tuint)
                  tulong)))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _b (tarray tuint 14))
                    (Etempvar _i tuint) (tptr tuint)) tuint)
                (Ebinop Oand (Etempvar _temp tulong)
                  (Econst_int (Int.repr (-1)) tuint) tulong))
              (Sset _temp
                (Ebinop Oshr (Etempvar _temp tulong)
                  (Econst_int (Int.repr 32) tint) tulong)))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Ssequence
      (Sset _h
        (Ebinop Oadd (Etempvar _h tuint)
          (Ebinop Osub (Ecast (Etempvar _temp tulong) tuint)
            (Econst_int (Int.repr 1) tint) tuint) tuint))
      (Scall None
        (Evar _curve448Select (Tfunction
                                (Tcons (tptr tuint)
                                  (Tcons (tptr tuint)
                                    (Tcons (tptr tuint) (Tcons tuint Tnil))))
                                tvoid cc_default))
        ((Etempvar _r (tptr tuint)) :: (Evar _b (tarray tuint 14)) ::
         (Etempvar _a (tptr tuint)) ::
         (Ebinop Oand (Etempvar _h tuint) (Econst_int (Int.repr 1) tint)
           tuint) :: nil)))))
|}.

Definition f_curve448Inv := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuint)) :: (_a, (tptr tuint)) :: nil);
  fn_vars := ((_u, (tarray tuint 14)) :: (_v, (tarray tuint 14)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _curve448Sqr (Tfunction
                         (Tcons (tptr tuint) (Tcons (tptr tuint) Tnil)) tvoid
                         cc_default))
    ((Evar _u (tarray tuint 14)) :: (Etempvar _a (tptr tuint)) :: nil))
  (Ssequence
    (Scall None
      (Evar _curve448Mul (Tfunction
                           (Tcons (tptr tuint)
                             (Tcons (tptr tuint) (Tcons (tptr tuint) Tnil)))
                           tvoid cc_default))
      ((Evar _u (tarray tuint 14)) :: (Evar _u (tarray tuint 14)) ::
       (Etempvar _a (tptr tuint)) :: nil))
    (Ssequence
      (Scall None
        (Evar _curve448Sqr (Tfunction
                             (Tcons (tptr tuint) (Tcons (tptr tuint) Tnil))
                             tvoid cc_default))
        ((Evar _u (tarray tuint 14)) :: (Evar _u (tarray tuint 14)) :: nil))
      (Ssequence
        (Scall None
          (Evar _curve448Mul (Tfunction
                               (Tcons (tptr tuint)
                                 (Tcons (tptr tuint)
                                   (Tcons (tptr tuint) Tnil))) tvoid
                               cc_default))
          ((Evar _v (tarray tuint 14)) :: (Evar _u (tarray tuint 14)) ::
           (Etempvar _a (tptr tuint)) :: nil))
        (Ssequence
          (Scall None
            (Evar _curve448Pwr2 (Tfunction
                                  (Tcons (tptr tuint)
                                    (Tcons (tptr tuint) (Tcons tuint Tnil)))
                                  tvoid cc_default))
            ((Evar _u (tarray tuint 14)) :: (Evar _v (tarray tuint 14)) ::
             (Econst_int (Int.repr 3) tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _curve448Mul (Tfunction
                                   (Tcons (tptr tuint)
                                     (Tcons (tptr tuint)
                                       (Tcons (tptr tuint) Tnil))) tvoid
                                   cc_default))
              ((Evar _v (tarray tuint 14)) :: (Evar _u (tarray tuint 14)) ::
               (Evar _v (tarray tuint 14)) :: nil))
            (Ssequence
              (Scall None
                (Evar _curve448Pwr2 (Tfunction
                                      (Tcons (tptr tuint)
                                        (Tcons (tptr tuint)
                                          (Tcons tuint Tnil))) tvoid
                                      cc_default))
                ((Evar _u (tarray tuint 14)) ::
                 (Evar _v (tarray tuint 14)) ::
                 (Econst_int (Int.repr 6) tint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _curve448Mul (Tfunction
                                       (Tcons (tptr tuint)
                                         (Tcons (tptr tuint)
                                           (Tcons (tptr tuint) Tnil))) tvoid
                                       cc_default))
                  ((Evar _u (tarray tuint 14)) ::
                   (Evar _u (tarray tuint 14)) ::
                   (Evar _v (tarray tuint 14)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _curve448Sqr (Tfunction
                                         (Tcons (tptr tuint)
                                           (Tcons (tptr tuint) Tnil)) tvoid
                                         cc_default))
                    ((Evar _u (tarray tuint 14)) ::
                     (Evar _u (tarray tuint 14)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _curve448Mul (Tfunction
                                           (Tcons (tptr tuint)
                                             (Tcons (tptr tuint)
                                               (Tcons (tptr tuint) Tnil)))
                                           tvoid cc_default))
                      ((Evar _v (tarray tuint 14)) ::
                       (Evar _u (tarray tuint 14)) ::
                       (Etempvar _a (tptr tuint)) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _curve448Pwr2 (Tfunction
                                              (Tcons (tptr tuint)
                                                (Tcons (tptr tuint)
                                                  (Tcons tuint Tnil))) tvoid
                                              cc_default))
                        ((Evar _u (tarray tuint 14)) ::
                         (Evar _v (tarray tuint 14)) ::
                         (Econst_int (Int.repr 13) tint) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _curve448Mul (Tfunction
                                               (Tcons (tptr tuint)
                                                 (Tcons (tptr tuint)
                                                   (Tcons (tptr tuint) Tnil)))
                                               tvoid cc_default))
                          ((Evar _u (tarray tuint 14)) ::
                           (Evar _u (tarray tuint 14)) ::
                           (Evar _v (tarray tuint 14)) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _curve448Sqr (Tfunction
                                                 (Tcons (tptr tuint)
                                                   (Tcons (tptr tuint) Tnil))
                                                 tvoid cc_default))
                            ((Evar _u (tarray tuint 14)) ::
                             (Evar _u (tarray tuint 14)) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _curve448Mul (Tfunction
                                                   (Tcons (tptr tuint)
                                                     (Tcons (tptr tuint)
                                                       (Tcons (tptr tuint)
                                                         Tnil))) tvoid
                                                   cc_default))
                              ((Evar _v (tarray tuint 14)) ::
                               (Evar _u (tarray tuint 14)) ::
                               (Etempvar _a (tptr tuint)) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _curve448Pwr2 (Tfunction
                                                      (Tcons (tptr tuint)
                                                        (Tcons (tptr tuint)
                                                          (Tcons tuint Tnil)))
                                                      tvoid cc_default))
                                ((Evar _u (tarray tuint 14)) ::
                                 (Evar _v (tarray tuint 14)) ::
                                 (Econst_int (Int.repr 27) tint) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar _curve448Mul (Tfunction
                                                       (Tcons (tptr tuint)
                                                         (Tcons (tptr tuint)
                                                           (Tcons
                                                             (tptr tuint)
                                                             Tnil))) tvoid
                                                       cc_default))
                                  ((Evar _u (tarray tuint 14)) ::
                                   (Evar _u (tarray tuint 14)) ::
                                   (Evar _v (tarray tuint 14)) :: nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _curve448Sqr (Tfunction
                                                         (Tcons (tptr tuint)
                                                           (Tcons
                                                             (tptr tuint)
                                                             Tnil)) tvoid
                                                         cc_default))
                                    ((Evar _u (tarray tuint 14)) ::
                                     (Evar _u (tarray tuint 14)) :: nil))
                                  (Ssequence
                                    (Scall None
                                      (Evar _curve448Mul (Tfunction
                                                           (Tcons
                                                             (tptr tuint)
                                                             (Tcons
                                                               (tptr tuint)
                                                               (Tcons
                                                                 (tptr tuint)
                                                                 Tnil)))
                                                           tvoid cc_default))
                                      ((Evar _v (tarray tuint 14)) ::
                                       (Evar _u (tarray tuint 14)) ::
                                       (Etempvar _a (tptr tuint)) :: nil))
                                    (Ssequence
                                      (Scall None
                                        (Evar _curve448Pwr2 (Tfunction
                                                              (Tcons
                                                                (tptr tuint)
                                                                (Tcons
                                                                  (tptr tuint)
                                                                  (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                              tvoid
                                                              cc_default))
                                        ((Evar _u (tarray tuint 14)) ::
                                         (Evar _v (tarray tuint 14)) ::
                                         (Econst_int (Int.repr 55) tint) ::
                                         nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _curve448Mul (Tfunction
                                                               (Tcons
                                                                 (tptr tuint)
                                                                 (Tcons
                                                                   (tptr tuint)
                                                                   (Tcons
                                                                    (tptr tuint)
                                                                    Tnil)))
                                                               tvoid
                                                               cc_default))
                                          ((Evar _u (tarray tuint 14)) ::
                                           (Evar _u (tarray tuint 14)) ::
                                           (Evar _v (tarray tuint 14)) ::
                                           nil))
                                        (Ssequence
                                          (Scall None
                                            (Evar _curve448Sqr (Tfunction
                                                                 (Tcons
                                                                   (tptr tuint)
                                                                   (Tcons
                                                                    (tptr tuint)
                                                                    Tnil))
                                                                 tvoid
                                                                 cc_default))
                                            ((Evar _u (tarray tuint 14)) ::
                                             (Evar _u (tarray tuint 14)) ::
                                             nil))
                                          (Ssequence
                                            (Scall None
                                              (Evar _curve448Mul (Tfunction
                                                                   (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil)))
                                                                   tvoid
                                                                   cc_default))
                                              ((Evar _v (tarray tuint 14)) ::
                                               (Evar _u (tarray tuint 14)) ::
                                               (Etempvar _a (tptr tuint)) ::
                                               nil))
                                            (Ssequence
                                              (Scall None
                                                (Evar _curve448Pwr2 (Tfunction
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                ((Evar _u (tarray tuint 14)) ::
                                                 (Evar _v (tarray tuint 14)) ::
                                                 (Econst_int (Int.repr 111) tint) ::
                                                 nil))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _curve448Mul 
                                                  (Tfunction
                                                    (Tcons (tptr tuint)
                                                      (Tcons (tptr tuint)
                                                        (Tcons (tptr tuint)
                                                          Tnil))) tvoid
                                                    cc_default))
                                                  ((Evar _v (tarray tuint 14)) ::
                                                   (Evar _u (tarray tuint 14)) ::
                                                   (Evar _v (tarray tuint 14)) ::
                                                   nil))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _curve448Sqr 
                                                    (Tfunction
                                                      (Tcons (tptr tuint)
                                                        (Tcons (tptr tuint)
                                                          Tnil)) tvoid
                                                      cc_default))
                                                    ((Evar _u (tarray tuint 14)) ::
                                                     (Evar _v (tarray tuint 14)) ::
                                                     nil))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _curve448Mul 
                                                      (Tfunction
                                                        (Tcons (tptr tuint)
                                                          (Tcons (tptr tuint)
                                                            (Tcons
                                                              (tptr tuint)
                                                              Tnil))) tvoid
                                                        cc_default))
                                                      ((Evar _u (tarray tuint 14)) ::
                                                       (Evar _u (tarray tuint 14)) ::
                                                       (Etempvar _a (tptr tuint)) ::
                                                       nil))
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _curve448Pwr2 
                                                        (Tfunction
                                                          (Tcons (tptr tuint)
                                                            (Tcons
                                                              (tptr tuint)
                                                              (Tcons tuint
                                                                Tnil))) tvoid
                                                          cc_default))
                                                        ((Evar _u (tarray tuint 14)) ::
                                                         (Evar _u (tarray tuint 14)) ::
                                                         (Econst_int (Int.repr 223) tint) ::
                                                         nil))
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _curve448Mul 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr tuint)
                                                              (Tcons
                                                                (tptr tuint)
                                                                (Tcons
                                                                  (tptr tuint)
                                                                  Tnil)))
                                                            tvoid cc_default))
                                                          ((Evar _u (tarray tuint 14)) ::
                                                           (Evar _u (tarray tuint 14)) ::
                                                           (Evar _v (tarray tuint 14)) ::
                                                           nil))
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _curve448Sqr 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr tuint)
                                                                (Tcons
                                                                  (tptr tuint)
                                                                  Tnil))
                                                              tvoid
                                                              cc_default))
                                                            ((Evar _u (tarray tuint 14)) ::
                                                             (Evar _u (tarray tuint 14)) ::
                                                             nil))
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _curve448Sqr 
                                                              (Tfunction
                                                                (Tcons
                                                                  (tptr tuint)
                                                                  (Tcons
                                                                    (tptr tuint)
                                                                    Tnil))
                                                                tvoid
                                                                cc_default))
                                                              ((Evar _u (tarray tuint 14)) ::
                                                               (Evar _u (tarray tuint 14)) ::
                                                               nil))
                                                            (Scall None
                                                              (Evar _curve448Mul 
                                                              (Tfunction
                                                                (Tcons
                                                                  (tptr tuint)
                                                                  (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil)))
                                                                tvoid
                                                                cc_default))
                                                              ((Etempvar _r (tptr tuint)) ::
                                                               (Evar _u (tarray tuint 14)) ::
                                                               (Etempvar _a (tptr tuint)) ::
                                                               nil))))))))))))))))))))))))))))))))
|}.

Definition f_curve448Sqrt := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuint)) :: (_a, (tptr tuint)) ::
                (_b, (tptr tuint)) :: nil);
  fn_vars := ((_c, (tarray tuint 14)) :: (_u, (tarray tuint 14)) ::
              (_v, (tarray tuint 14)) :: nil);
  fn_temps := ((_res, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _curve448Sqr (Tfunction
                         (Tcons (tptr tuint) (Tcons (tptr tuint) Tnil)) tvoid
                         cc_default))
    ((Evar _u (tarray tuint 14)) :: (Etempvar _a (tptr tuint)) :: nil))
  (Ssequence
    (Scall None
      (Evar _curve448Sqr (Tfunction
                           (Tcons (tptr tuint) (Tcons (tptr tuint) Tnil))
                           tvoid cc_default))
      ((Evar _u (tarray tuint 14)) :: (Evar _u (tarray tuint 14)) :: nil))
    (Ssequence
      (Scall None
        (Evar _curve448Mul (Tfunction
                             (Tcons (tptr tuint)
                               (Tcons (tptr tuint) (Tcons (tptr tuint) Tnil)))
                             tvoid cc_default))
        ((Evar _u (tarray tuint 14)) :: (Evar _u (tarray tuint 14)) ::
         (Etempvar _a (tptr tuint)) :: nil))
      (Ssequence
        (Scall None
          (Evar _curve448Sqr (Tfunction
                               (Tcons (tptr tuint) (Tcons (tptr tuint) Tnil))
                               tvoid cc_default))
          ((Evar _v (tarray tuint 14)) :: (Etempvar _b (tptr tuint)) :: nil))
        (Ssequence
          (Scall None
            (Evar _curve448Mul (Tfunction
                                 (Tcons (tptr tuint)
                                   (Tcons (tptr tuint)
                                     (Tcons (tptr tuint) Tnil))) tvoid
                                 cc_default))
            ((Evar _v (tarray tuint 14)) :: (Evar _v (tarray tuint 14)) ::
             (Etempvar _b (tptr tuint)) :: nil))
          (Ssequence
            (Scall None
              (Evar _curve448Mul (Tfunction
                                   (Tcons (tptr tuint)
                                     (Tcons (tptr tuint)
                                       (Tcons (tptr tuint) Tnil))) tvoid
                                   cc_default))
              ((Evar _c (tarray tuint 14)) :: (Evar _u (tarray tuint 14)) ::
               (Evar _v (tarray tuint 14)) :: nil))
            (Ssequence
              (Scall None
                (Evar _curve448Sqr (Tfunction
                                     (Tcons (tptr tuint)
                                       (Tcons (tptr tuint) Tnil)) tvoid
                                     cc_default))
                ((Evar _u (tarray tuint 14)) ::
                 (Evar _c (tarray tuint 14)) :: nil))
              (Ssequence
                (Scall None
                  (Evar _curve448Mul (Tfunction
                                       (Tcons (tptr tuint)
                                         (Tcons (tptr tuint)
                                           (Tcons (tptr tuint) Tnil))) tvoid
                                       cc_default))
                  ((Evar _u (tarray tuint 14)) ::
                   (Evar _u (tarray tuint 14)) ::
                   (Evar _c (tarray tuint 14)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _curve448Sqr (Tfunction
                                         (Tcons (tptr tuint)
                                           (Tcons (tptr tuint) Tnil)) tvoid
                                         cc_default))
                    ((Evar _u (tarray tuint 14)) ::
                     (Evar _u (tarray tuint 14)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _curve448Mul (Tfunction
                                           (Tcons (tptr tuint)
                                             (Tcons (tptr tuint)
                                               (Tcons (tptr tuint) Tnil)))
                                           tvoid cc_default))
                      ((Evar _v (tarray tuint 14)) ::
                       (Evar _u (tarray tuint 14)) ::
                       (Evar _c (tarray tuint 14)) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _curve448Pwr2 (Tfunction
                                              (Tcons (tptr tuint)
                                                (Tcons (tptr tuint)
                                                  (Tcons tuint Tnil))) tvoid
                                              cc_default))
                        ((Evar _u (tarray tuint 14)) ::
                         (Evar _v (tarray tuint 14)) ::
                         (Econst_int (Int.repr 3) tint) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _curve448Mul (Tfunction
                                               (Tcons (tptr tuint)
                                                 (Tcons (tptr tuint)
                                                   (Tcons (tptr tuint) Tnil)))
                                               tvoid cc_default))
                          ((Evar _v (tarray tuint 14)) ::
                           (Evar _u (tarray tuint 14)) ::
                           (Evar _v (tarray tuint 14)) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _curve448Pwr2 (Tfunction
                                                  (Tcons (tptr tuint)
                                                    (Tcons (tptr tuint)
                                                      (Tcons tuint Tnil)))
                                                  tvoid cc_default))
                            ((Evar _u (tarray tuint 14)) ::
                             (Evar _v (tarray tuint 14)) ::
                             (Econst_int (Int.repr 6) tint) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _curve448Mul (Tfunction
                                                   (Tcons (tptr tuint)
                                                     (Tcons (tptr tuint)
                                                       (Tcons (tptr tuint)
                                                         Tnil))) tvoid
                                                   cc_default))
                              ((Evar _u (tarray tuint 14)) ::
                               (Evar _u (tarray tuint 14)) ::
                               (Evar _v (tarray tuint 14)) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _curve448Sqr (Tfunction
                                                     (Tcons (tptr tuint)
                                                       (Tcons (tptr tuint)
                                                         Tnil)) tvoid
                                                     cc_default))
                                ((Evar _u (tarray tuint 14)) ::
                                 (Evar _u (tarray tuint 14)) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar _curve448Mul (Tfunction
                                                       (Tcons (tptr tuint)
                                                         (Tcons (tptr tuint)
                                                           (Tcons
                                                             (tptr tuint)
                                                             Tnil))) tvoid
                                                       cc_default))
                                  ((Evar _v (tarray tuint 14)) ::
                                   (Evar _u (tarray tuint 14)) ::
                                   (Evar _c (tarray tuint 14)) :: nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _curve448Pwr2 (Tfunction
                                                          (Tcons (tptr tuint)
                                                            (Tcons
                                                              (tptr tuint)
                                                              (Tcons tuint
                                                                Tnil))) tvoid
                                                          cc_default))
                                    ((Evar _u (tarray tuint 14)) ::
                                     (Evar _v (tarray tuint 14)) ::
                                     (Econst_int (Int.repr 13) tint) :: nil))
                                  (Ssequence
                                    (Scall None
                                      (Evar _curve448Mul (Tfunction
                                                           (Tcons
                                                             (tptr tuint)
                                                             (Tcons
                                                               (tptr tuint)
                                                               (Tcons
                                                                 (tptr tuint)
                                                                 Tnil)))
                                                           tvoid cc_default))
                                      ((Evar _u (tarray tuint 14)) ::
                                       (Evar _u (tarray tuint 14)) ::
                                       (Evar _v (tarray tuint 14)) :: nil))
                                    (Ssequence
                                      (Scall None
                                        (Evar _curve448Sqr (Tfunction
                                                             (Tcons
                                                               (tptr tuint)
                                                               (Tcons
                                                                 (tptr tuint)
                                                                 Tnil)) tvoid
                                                             cc_default))
                                        ((Evar _u (tarray tuint 14)) ::
                                         (Evar _u (tarray tuint 14)) :: nil))
                                      (Ssequence
                                        (Scall None
                                          (Evar _curve448Mul (Tfunction
                                                               (Tcons
                                                                 (tptr tuint)
                                                                 (Tcons
                                                                   (tptr tuint)
                                                                   (Tcons
                                                                    (tptr tuint)
                                                                    Tnil)))
                                                               tvoid
                                                               cc_default))
                                          ((Evar _v (tarray tuint 14)) ::
                                           (Evar _u (tarray tuint 14)) ::
                                           (Evar _c (tarray tuint 14)) ::
                                           nil))
                                        (Ssequence
                                          (Scall None
                                            (Evar _curve448Pwr2 (Tfunction
                                                                  (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                  tvoid
                                                                  cc_default))
                                            ((Evar _u (tarray tuint 14)) ::
                                             (Evar _v (tarray tuint 14)) ::
                                             (Econst_int (Int.repr 27) tint) ::
                                             nil))
                                          (Ssequence
                                            (Scall None
                                              (Evar _curve448Mul (Tfunction
                                                                   (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil)))
                                                                   tvoid
                                                                   cc_default))
                                              ((Evar _u (tarray tuint 14)) ::
                                               (Evar _u (tarray tuint 14)) ::
                                               (Evar _v (tarray tuint 14)) ::
                                               nil))
                                            (Ssequence
                                              (Scall None
                                                (Evar _curve448Sqr (Tfunction
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                ((Evar _u (tarray tuint 14)) ::
                                                 (Evar _u (tarray tuint 14)) ::
                                                 nil))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _curve448Mul 
                                                  (Tfunction
                                                    (Tcons (tptr tuint)
                                                      (Tcons (tptr tuint)
                                                        (Tcons (tptr tuint)
                                                          Tnil))) tvoid
                                                    cc_default))
                                                  ((Evar _v (tarray tuint 14)) ::
                                                   (Evar _u (tarray tuint 14)) ::
                                                   (Evar _c (tarray tuint 14)) ::
                                                   nil))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _curve448Pwr2 
                                                    (Tfunction
                                                      (Tcons (tptr tuint)
                                                        (Tcons (tptr tuint)
                                                          (Tcons tuint Tnil)))
                                                      tvoid cc_default))
                                                    ((Evar _u (tarray tuint 14)) ::
                                                     (Evar _v (tarray tuint 14)) ::
                                                     (Econst_int (Int.repr 55) tint) ::
                                                     nil))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _curve448Mul 
                                                      (Tfunction
                                                        (Tcons (tptr tuint)
                                                          (Tcons (tptr tuint)
                                                            (Tcons
                                                              (tptr tuint)
                                                              Tnil))) tvoid
                                                        cc_default))
                                                      ((Evar _u (tarray tuint 14)) ::
                                                       (Evar _u (tarray tuint 14)) ::
                                                       (Evar _v (tarray tuint 14)) ::
                                                       nil))
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _curve448Sqr 
                                                        (Tfunction
                                                          (Tcons (tptr tuint)
                                                            (Tcons
                                                              (tptr tuint)
                                                              Tnil)) tvoid
                                                          cc_default))
                                                        ((Evar _u (tarray tuint 14)) ::
                                                         (Evar _u (tarray tuint 14)) ::
                                                         nil))
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _curve448Mul 
                                                          (Tfunction
                                                            (Tcons
                                                              (tptr tuint)
                                                              (Tcons
                                                                (tptr tuint)
                                                                (Tcons
                                                                  (tptr tuint)
                                                                  Tnil)))
                                                            tvoid cc_default))
                                                          ((Evar _v (tarray tuint 14)) ::
                                                           (Evar _u (tarray tuint 14)) ::
                                                           (Evar _c (tarray tuint 14)) ::
                                                           nil))
                                                        (Ssequence
                                                          (Scall None
                                                            (Evar _curve448Pwr2 
                                                            (Tfunction
                                                              (Tcons
                                                                (tptr tuint)
                                                                (Tcons
                                                                  (tptr tuint)
                                                                  (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                              tvoid
                                                              cc_default))
                                                            ((Evar _u (tarray tuint 14)) ::
                                                             (Evar _v (tarray tuint 14)) ::
                                                             (Econst_int (Int.repr 111) tint) ::
                                                             nil))
                                                          (Ssequence
                                                            (Scall None
                                                              (Evar _curve448Mul 
                                                              (Tfunction
                                                                (Tcons
                                                                  (tptr tuint)
                                                                  (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil)))
                                                                tvoid
                                                                cc_default))
                                                              ((Evar _v (tarray tuint 14)) ::
                                                               (Evar _u (tarray tuint 14)) ::
                                                               (Evar _v (tarray tuint 14)) ::
                                                               nil))
                                                            (Ssequence
                                                              (Scall None
                                                                (Evar _curve448Sqr 
                                                                (Tfunction
                                                                  (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil))
                                                                  tvoid
                                                                  cc_default))
                                                                ((Evar _u (tarray tuint 14)) ::
                                                                 (Evar _v (tarray tuint 14)) ::
                                                                 nil))
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _curve448Mul 
                                                                  (Tfunction
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Evar _u (tarray tuint 14)) ::
                                                                   (Evar _u (tarray tuint 14)) ::
                                                                   (Evar _c (tarray tuint 14)) ::
                                                                   nil))
                                                                (Ssequence
                                                                  (Scall None
                                                                    (Evar _curve448Pwr2 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _u (tarray tuint 14)) ::
                                                                    (Evar _u (tarray tuint 14)) ::
                                                                    (Econst_int (Int.repr 223) tint) ::
                                                                    nil))
                                                                  (Ssequence
                                                                    (Scall None
                                                                    (Evar _curve448Mul 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _u (tarray tuint 14)) ::
                                                                    (Evar _u (tarray tuint 14)) ::
                                                                    (Evar _v (tarray tuint 14)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _curve448Sqr 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _v (tarray tuint 14)) ::
                                                                    (Etempvar _a (tptr tuint)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _curve448Mul 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _v (tarray tuint 14)) ::
                                                                    (Evar _v (tarray tuint 14)) ::
                                                                    (Etempvar _a (tptr tuint)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _curve448Mul 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _u (tarray tuint 14)) ::
                                                                    (Evar _u (tarray tuint 14)) ::
                                                                    (Evar _v (tarray tuint 14)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _curve448Mul 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _u (tarray tuint 14)) ::
                                                                    (Evar _u (tarray tuint 14)) ::
                                                                    (Etempvar _b (tptr tuint)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _curve448Sqr 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _c (tarray tuint 14)) ::
                                                                    (Evar _u (tarray tuint 14)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _curve448Mul 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil)))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _c (tarray tuint 14)) ::
                                                                    (Evar _c (tarray tuint 14)) ::
                                                                    (Etempvar _b (tptr tuint)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'1)
                                                                    (Evar _curve448Comp 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil))
                                                                    tuint
                                                                    cc_default))
                                                                    ((Evar _c (tarray tuint 14)) ::
                                                                    (Etempvar _a (tptr tuint)) ::
                                                                    nil))
                                                                    (Sset _res
                                                                    (Etempvar _t'1 tuint)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _curve448Copy 
                                                                    (Tfunction
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    (Tcons
                                                                    (tptr tuint)
                                                                    Tnil))
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _r (tptr tuint)) ::
                                                                    (Evar _u (tarray tuint 14)) ::
                                                                    nil))
                                                                    (Sreturn (Some (Etempvar _res tuint)))))))))))))))))))))))))))))))))))))))))))))
|}.

Definition f_curve448Copy := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tuint)) :: (_b, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                     (Econst_int (Int.repr 14) tint) tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd (Etempvar _b (tptr tuint)) (Etempvar _i tuint)
              (tptr tuint)) tuint))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _a (tptr tuint)) (Etempvar _i tuint)
              (tptr tuint)) tuint) (Etempvar _t'1 tuint))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint) tuint))))
|}.

Definition f_curve448Swap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tuint)) :: (_b, (tptr tuint)) :: (_c, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_mask, tuint) :: (_dummy, tuint) ::
               (_t'4, tuint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _mask
    (Ebinop Oadd (Eunop Onotint (Etempvar _c tuint) tuint)
      (Econst_int (Int.repr 1) tint) tuint))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                       (Econst_int (Int.repr 14) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Ederef
                (Ebinop Oadd (Etempvar _a (tptr tuint)) (Etempvar _i tuint)
                  (tptr tuint)) tuint))
            (Ssequence
              (Sset _t'4
                (Ederef
                  (Ebinop Oadd (Etempvar _b (tptr tuint)) (Etempvar _i tuint)
                    (tptr tuint)) tuint))
              (Sset _dummy
                (Ebinop Oand (Etempvar _mask tuint)
                  (Ebinop Oxor (Etempvar _t'3 tuint) (Etempvar _t'4 tuint)
                    tuint) tuint))))
          (Ssequence
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Etempvar _a (tptr tuint)) (Etempvar _i tuint)
                    (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _a (tptr tuint)) (Etempvar _i tuint)
                    (tptr tuint)) tuint)
                (Ebinop Oxor (Etempvar _t'2 tuint) (Etempvar _dummy tuint)
                  tuint)))
            (Ssequence
              (Sset _t'1
                (Ederef
                  (Ebinop Oadd (Etempvar _b (tptr tuint)) (Etempvar _i tuint)
                    (tptr tuint)) tuint))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Etempvar _b (tptr tuint)) (Etempvar _i tuint)
                    (tptr tuint)) tuint)
                (Ebinop Oxor (Etempvar _t'1 tuint) (Etempvar _dummy tuint)
                  tuint))))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint)))))
|}.

Definition f_curve448Select := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuint)) :: (_a, (tptr tuint)) ::
                (_b, (tptr tuint)) :: (_c, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_mask, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _mask
    (Ebinop Osub (Etempvar _c tuint) (Econst_int (Int.repr 1) tint) tuint))
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                       (Econst_int (Int.repr 14) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd (Etempvar _a (tptr tuint)) (Etempvar _i tuint)
                (tptr tuint)) tuint))
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Etempvar _b (tptr tuint)) (Etempvar _i tuint)
                  (tptr tuint)) tuint))
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _r (tptr tuint)) (Etempvar _i tuint)
                  (tptr tuint)) tuint)
              (Ebinop Oor
                (Ebinop Oand (Etempvar _t'1 tuint) (Etempvar _mask tuint)
                  tuint)
                (Ebinop Oand (Etempvar _t'2 tuint)
                  (Eunop Onotint (Etempvar _mask tuint) tuint) tuint) tuint)))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
          tuint)))))
|}.

Definition f_curve448Comp := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tuint)) :: (_b, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_mask, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _mask (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                         (Econst_int (Int.repr 14) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'1
              (Ederef
                (Ebinop Oadd (Etempvar _a (tptr tuint)) (Etempvar _i tuint)
                  (tptr tuint)) tuint))
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Etempvar _b (tptr tuint)) (Etempvar _i tuint)
                    (tptr tuint)) tuint))
              (Sset _mask
                (Ebinop Oor (Etempvar _mask tuint)
                  (Ebinop Oxor (Etempvar _t'1 tuint) (Etempvar _t'2 tuint)
                    tuint) tuint)))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Sreturn (Some (Ebinop Oshr
                     (Ecast
                       (Ebinop Oor (Etempvar _mask tuint)
                         (Ebinop Oadd
                           (Eunop Onotint (Etempvar _mask tuint) tuint)
                           (Econst_int (Int.repr 1) tint) tuint) tuint)
                       tuint) (Econst_int (Int.repr 31) tint) tuint)))))
|}.

Definition composites : list composite_definition :=
nil.

Definition global_definitions : list (ident * globdef fundef type) :=
((___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_curve448SetInt, Gfun(Internal f_curve448SetInt)) ::
 (_curve448Add, Gfun(Internal f_curve448Add)) ::
 (_curve448AddInt, Gfun(Internal f_curve448AddInt)) ::
 (_curve448Sub, Gfun(Internal f_curve448Sub)) ::
 (_curve448SubInt, Gfun(Internal f_curve448SubInt)) ::
 (_curve448Mul, Gfun(Internal f_curve448Mul)) ::
 (_curve448MulInt, Gfun(Internal f_curve448MulInt)) ::
 (_curve448Sqr, Gfun(Internal f_curve448Sqr)) ::
 (_curve448Pwr2, Gfun(Internal f_curve448Pwr2)) ::
 (_curve448Red, Gfun(Internal f_curve448Red)) ::
 (_curve448Inv, Gfun(Internal f_curve448Inv)) ::
 (_curve448Sqrt, Gfun(Internal f_curve448Sqrt)) ::
 (_curve448Copy, Gfun(Internal f_curve448Copy)) ::
 (_curve448Swap, Gfun(Internal f_curve448Swap)) ::
 (_curve448Select, Gfun(Internal f_curve448Select)) ::
 (_curve448Comp, Gfun(Internal f_curve448Comp)) :: nil).

Definition public_idents : list ident :=
(_curve448Comp :: _curve448Select :: _curve448Swap :: _curve448Copy ::
 _curve448Sqrt :: _curve448Inv :: _curve448Red :: _curve448Pwr2 ::
 _curve448Sqr :: _curve448MulInt :: _curve448Mul :: _curve448SubInt ::
 _curve448Sub :: _curve448AddInt :: _curve448Add :: _curve448SetInt ::
 ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___builtin_expect :: ___builtin_unreachable ::
 ___compcert_va_composite :: ___compcert_va_float64 ::
 ___compcert_va_int64 :: ___compcert_va_int32 :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


