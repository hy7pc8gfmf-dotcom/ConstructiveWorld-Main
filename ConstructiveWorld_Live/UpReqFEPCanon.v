(* ==========================================================================)
   UpReqFEPCanon.v — FEP 规范形的 KL 分解恒等式
   使命: real_kl_decomp_full_canon 及其分划版本：UpReqRealFEP 语境束在规范实例上的逐字材料化（恒等式与分划两件）。
   依赖: CW_ConstructiveWorld_219、UpReqRealFEP。
   对标: KL 分解恒等式的规范实例层。
   构造性: 全件 Qed 闭合、零承认词面、无经典逻辑；语句面以 Set 层承载（序谓词与等词为 Set 值，零 Prop 泄露）。
   编译配方: Rocq 9.1 直调 coqc -Q . "" -native-compiler no（vo 影子树同世界重编），cpu_guard 包裹限载。
   ========================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqRealFEP.

(* ---------------------------------------------------------- *)
(* 主件：real_kl_decomp_full_canon                                   *)
(*   S08 参数 real_kl_decomp_full 的正典化消解形：结论面与 S08 参数位逐字    *)
(*   同构（real_eq (F p) (F p_b + D·Σ kl_term)）；节接口按消解后全参   *)
(*   显式升参（含 rfep 版诚实增量 linear），残留前提 Hnormb 照单升参。 *)
(*   证明 = rfep_real_kl_decomp_full 部分应用显式应用（一步 exact）。     *)
(* ---------------------------------------------------------- *)

Lemma real_kl_decomp_full_canon :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
  real_eq (real_sum_over_S p) real_one ->
  real_eq (real_sum_over_S
             (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos))
          real_one ->
  real_eq (real_free_energy S real_sum_over_S real_base_loss D p Hp)
          (real_plus
             (real_free_energy S real_sum_over_S real_base_loss D
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))
             (real_mult D
                (real_sum_over_S
                   (fun s : S => real_kl_term (p s)
                      (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                      (Hp s)
                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))).
Proof.
  intros S real_sum_over_S real_sum_over_S_ext real_sum_over_S_add         real_sum_over_S_linear real_base_loss D D_pos Z_align_r Z_align_r_pos         p Hp Hnormp Hnormb.
  exact (rfep_real_kl_decomp_full           S real_sum_over_S real_sum_over_S_ext real_sum_over_S_add           real_sum_over_S_linear real_base_loss D D_pos Z_align_r Z_align_r_pos           p Hp Hnormp Hnormb).
Qed.

(* ---------------------------------------------------------- *)
(* 分件：real_kl_decomp_full_canon_partition（前提消解小链版）        *)
(*   与主件同结论面；Hnormb 换为 partition 条件 Hpart                  *)
(*   （Σ exp(−e/D) ≡ Z，物理配分函数清单），经 rfep_boltzmann_        *)
(*   normalized_real 一步消解补齐 Hnormb，再显式应用 rfep 主件。           *)
(* ---------------------------------------------------------- *)

Lemma real_kl_decomp_full_canon_partition :
  forall (S : Type) (real_sum_over_S : (S -> Real) -> Real),
  (forall f g : S -> Real,
    (forall s : S, real_eq (f s) (g s)) ->
    real_eq (real_sum_over_S f) (real_sum_over_S g)) ->
  (forall f g : S -> Real,
    real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
            (real_plus (real_sum_over_S f) (real_sum_over_S g))) ->
  (forall (a : Real) (f : S -> Real),
    real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
            (real_mult a (real_sum_over_S f))) ->
  forall (real_base_loss : S -> Real) (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
  real_eq (real_sum_over_S p) real_one ->
  real_eq (real_sum_over_S
             (fun s : S => real_exp_neg
                             (real_mult (real_inv_pos D D_pos) (real_base_loss s))))
          Z_align_r ->
  real_eq (real_free_energy S real_sum_over_S real_base_loss D p Hp)
          (real_plus
             (real_free_energy S real_sum_over_S real_base_loss D
                (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos)
                (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos))
             (real_mult D
                (real_sum_over_S
                   (fun s : S => real_kl_term (p s)
                      (real_boltzmann_dist_r S real_base_loss D D_pos Z_align_r Z_align_r_pos s)
                      (Hp s)
                      (real_boltzmann_dist_r_pos S real_base_loss D D_pos Z_align_r Z_align_r_pos s))))).
Proof.
  intros S real_sum_over_S real_sum_over_S_ext real_sum_over_S_add         real_sum_over_S_linear real_base_loss D D_pos Z_align_r Z_align_r_pos         p Hp Hnormp Hpart.
  apply (rfep_real_kl_decomp_full           S real_sum_over_S real_sum_over_S_ext real_sum_over_S_add           real_sum_over_S_linear real_base_loss D D_pos Z_align_r Z_align_r_pos           p Hp Hnormp).
  exact (rfep_boltzmann_normalized_real           S real_sum_over_S real_sum_over_S_ext real_sum_over_S_linear           real_base_loss D D_pos Z_align_r Z_align_r_pos Hpart).
Qed.
