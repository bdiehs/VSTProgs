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
  Definition source_file := "src/splay.c".
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
Definition _ch : ident := $"ch".
Definition _g : ident := $"g".
Definition _key : ident := $"key".
Definition _left : ident := $"left".
Definition _main : ident := $"main".
Definition _node : ident := $"node".
Definition _p : ident := $"p".
Definition _parent : ident := $"parent".
Definition _right : ident := $"right".
Definition _root : ident := $"root".
Definition _rotate : ident := $"rotate".
Definition _splay : ident := $"splay".
Definition _value : ident := $"value".
Definition _x : ident := $"x".
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

Definition f_rotate := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_root, (tptr (tptr (Tstruct _node noattr)))) ::
                (_x, (tptr (Tstruct _node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _node noattr))) ::
               (_ch, (tptr (Tstruct _node noattr))) ::
               (_t'13, (tptr (Tstruct _node noattr))) ::
               (_t'12, (tptr (Tstruct _node noattr))) ::
               (_t'11, (tptr (Tstruct _node noattr))) ::
               (_t'10, (tptr (Tstruct _node noattr))) ::
               (_t'9, (tptr (Tstruct _node noattr))) ::
               (_t'8, (tptr (Tstruct _node noattr))) ::
               (_t'7, (tptr (Tstruct _node noattr))) ::
               (_t'6, (tptr (Tstruct _node noattr))) ::
               (_t'5, (tptr (Tstruct _node noattr))) ::
               (_t'4, (tptr (Tstruct _node noattr))) ::
               (_t'3, (tptr (Tstruct _node noattr))) ::
               (_t'2, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _p
    (Efield
      (Ederef (Etempvar _x (tptr (Tstruct _node noattr)))
        (Tstruct _node noattr)) _parent (tptr (Tstruct _node noattr))))
  (Ssequence
    (Ssequence
      (Sset _t'7
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
            (Tstruct _node noattr)) _left (tptr (Tstruct _node noattr))))
      (Sifthenelse (Ebinop Oeq (Etempvar _t'7 (tptr (Tstruct _node noattr)))
                     (Etempvar _x (tptr (Tstruct _node noattr))) tint)
        (Ssequence
          (Ssequence
            (Sset _t'13
              (Efield
                (Ederef (Etempvar _x (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _right
                (tptr (Tstruct _node noattr))))
            (Sassign
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _left
                (tptr (Tstruct _node noattr)))
              (Etempvar _t'13 (tptr (Tstruct _node noattr)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _x (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _right
                (tptr (Tstruct _node noattr)))
              (Etempvar _p (tptr (Tstruct _node noattr))))
            (Ssequence
              (Sset _t'11
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                    (Tstruct _node noattr)) _left
                  (tptr (Tstruct _node noattr))))
              (Sifthenelse (Etempvar _t'11 (tptr (Tstruct _node noattr)))
                (Ssequence
                  (Sset _t'12
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _left
                      (tptr (Tstruct _node noattr))))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _t'12 (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _parent
                      (tptr (Tstruct _node noattr)))
                    (Etempvar _p (tptr (Tstruct _node noattr)))))
                Sskip))))
        (Ssequence
          (Ssequence
            (Sset _t'10
              (Efield
                (Ederef (Etempvar _x (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _left
                (tptr (Tstruct _node noattr))))
            (Sassign
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _right
                (tptr (Tstruct _node noattr)))
              (Etempvar _t'10 (tptr (Tstruct _node noattr)))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _x (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _left
                (tptr (Tstruct _node noattr)))
              (Etempvar _p (tptr (Tstruct _node noattr))))
            (Ssequence
              (Sset _t'8
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                    (Tstruct _node noattr)) _right
                  (tptr (Tstruct _node noattr))))
              (Sifthenelse (Etempvar _t'8 (tptr (Tstruct _node noattr)))
                (Ssequence
                  (Sset _t'9
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _right
                      (tptr (Tstruct _node noattr))))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _t'9 (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _parent
                      (tptr (Tstruct _node noattr)))
                    (Etempvar _p (tptr (Tstruct _node noattr)))))
                Sskip))))))
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
              (Tstruct _node noattr)) _parent (tptr (Tstruct _node noattr))))
        (Sifthenelse (Etempvar _t'2 (tptr (Tstruct _node noattr)))
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                  (Tstruct _node noattr)) _parent
                (tptr (Tstruct _node noattr))))
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _t'3 (tptr (Tstruct _node noattr)))
                    (Tstruct _node noattr)) _left
                  (tptr (Tstruct _node noattr))))
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _t'4 (tptr (Tstruct _node noattr)))
                             (Etempvar _p (tptr (Tstruct _node noattr)))
                             tint)
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _parent
                      (tptr (Tstruct _node noattr))))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _t'6 (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _left
                      (tptr (Tstruct _node noattr)))
                    (Etempvar _x (tptr (Tstruct _node noattr)))))
                (Ssequence
                  (Sset _t'5
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _parent
                      (tptr (Tstruct _node noattr))))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _t'5 (tptr (Tstruct _node noattr)))
                        (Tstruct _node noattr)) _right
                      (tptr (Tstruct _node noattr)))
                    (Etempvar _x (tptr (Tstruct _node noattr))))))))
          (Sassign
            (Ederef (Etempvar _root (tptr (tptr (Tstruct _node noattr))))
              (tptr (Tstruct _node noattr)))
            (Etempvar _x (tptr (Tstruct _node noattr))))))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _parent
              (tptr (Tstruct _node noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _x (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _parent
              (tptr (Tstruct _node noattr)))
            (Etempvar _t'1 (tptr (Tstruct _node noattr)))))
        (Sassign
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
              (Tstruct _node noattr)) _parent (tptr (Tstruct _node noattr)))
          (Etempvar _x (tptr (Tstruct _node noattr))))))))
|}.

Definition f_splay := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_root, (tptr (tptr (Tstruct _node noattr)))) ::
                (_x, (tptr (Tstruct _node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr (Tstruct _node noattr))) ::
               (_g, (tptr (Tstruct _node noattr))) ::
               (_t'2, (tptr (Tstruct _node noattr))) ::
               (_t'1, (tptr (Tstruct _node noattr))) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    Sskip
    (Ssequence
      (Sset _p
        (Efield
          (Ederef (Etempvar _x (tptr (Tstruct _node noattr)))
            (Tstruct _node noattr)) _parent (tptr (Tstruct _node noattr))))
      (Ssequence
        (Sifthenelse (Ebinop Oeq (Etempvar _p (tptr (Tstruct _node noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Sreturn None)
          Sskip)
        (Ssequence
          (Sset _g
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                (Tstruct _node noattr)) _parent
              (tptr (Tstruct _node noattr))))
          (Ssequence
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _g (tptr (Tstruct _node noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Ssequence
                (Scall None
                  (Evar _rotate (Tfunction
                                  (Tcons (tptr (tptr (Tstruct _node noattr)))
                                    (Tcons (tptr (Tstruct _node noattr))
                                      Tnil)) tvoid cc_default))
                  ((Etempvar _root (tptr (tptr (Tstruct _node noattr)))) ::
                   (Etempvar _x (tptr (Tstruct _node noattr))) :: nil))
                (Sreturn None))
              Sskip)
            (Ssequence
              (Sset _t'1
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _node noattr)))
                    (Tstruct _node noattr)) _left
                  (tptr (Tstruct _node noattr))))
              (Ssequence
                (Sset _t'2
                  (Efield
                    (Ederef (Etempvar _g (tptr (Tstruct _node noattr)))
                      (Tstruct _node noattr)) _left
                    (tptr (Tstruct _node noattr))))
                (Sifthenelse (Ebinop Oeq
                               (Ebinop Oeq
                                 (Etempvar _t'1 (tptr (Tstruct _node noattr)))
                                 (Etempvar _x (tptr (Tstruct _node noattr)))
                                 tint)
                               (Ebinop Oeq
                                 (Etempvar _t'2 (tptr (Tstruct _node noattr)))
                                 (Etempvar _p (tptr (Tstruct _node noattr)))
                                 tint) tint)
                  (Ssequence
                    (Scall None
                      (Evar _rotate (Tfunction
                                      (Tcons
                                        (tptr (tptr (Tstruct _node noattr)))
                                        (Tcons (tptr (Tstruct _node noattr))
                                          Tnil)) tvoid cc_default))
                      ((Etempvar _root (tptr (tptr (Tstruct _node noattr)))) ::
                       (Etempvar _p (tptr (Tstruct _node noattr))) :: nil))
                    (Scall None
                      (Evar _rotate (Tfunction
                                      (Tcons
                                        (tptr (tptr (Tstruct _node noattr)))
                                        (Tcons (tptr (Tstruct _node noattr))
                                          Tnil)) tvoid cc_default))
                      ((Etempvar _root (tptr (tptr (Tstruct _node noattr)))) ::
                       (Etempvar _x (tptr (Tstruct _node noattr))) :: nil)))
                  (Ssequence
                    (Scall None
                      (Evar _rotate (Tfunction
                                      (Tcons
                                        (tptr (tptr (Tstruct _node noattr)))
                                        (Tcons (tptr (Tstruct _node noattr))
                                          Tnil)) tvoid cc_default))
                      ((Etempvar _root (tptr (tptr (Tstruct _node noattr)))) ::
                       (Etempvar _x (tptr (Tstruct _node noattr))) :: nil))
                    (Scall None
                      (Evar _rotate (Tfunction
                                      (Tcons
                                        (tptr (tptr (Tstruct _node noattr)))
                                        (Tcons (tptr (Tstruct _node noattr))
                                          Tnil)) tvoid cc_default))
                      ((Etempvar _root (tptr (tptr (Tstruct _node noattr)))) ::
                       (Etempvar _x (tptr (Tstruct _node noattr))) :: nil)))))))))))
  Sskip)
|}.

Definition composites : list composite_definition :=
(Composite _node Struct
   ((_key, tulong) :: (_value, (tptr tvoid)) ::
    (_left, (tptr (Tstruct _node noattr))) ::
    (_right, (tptr (Tstruct _node noattr))) ::
    (_parent, (tptr (Tstruct _node noattr))) :: nil)
   noattr :: nil).

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
 (_rotate, Gfun(Internal f_rotate)) :: (_splay, Gfun(Internal f_splay)) ::
 nil).

Definition public_idents : list ident :=
(_splay :: _rotate :: ___builtin_debug :: ___builtin_write32_reversed ::
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


