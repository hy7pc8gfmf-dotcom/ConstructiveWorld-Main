(* UpReqMinFreeEps.v *) (* 目的： 定理 4.4 min_free_energy 的 Real 层序档组装（eps 档）。 *)
(* 主件： min_free_energy_is_boltzmann_eps 及其配分形；min_free_energy_close_eps。 *) (* 依赖： CW_ConstructiveWorld_219、UpReqRealFEP、UpReqFEPCanon。 *)
(* 备注： 最小自由能的 Boltzmann 刻画取逐 eps 档；零新假设位。 *) (* 构造性注记：Set 层承载、零承认、可提取。 *)
(* 编译配方：rocq 9.1 直调 + cpu_guard。 *) (* UpReqMinFreeEps.v —— 定理 4.4 min_free_energy Real 层序档组装 *)
(* 使命：判定（C2）——定理 4.4（Boltzmann 分布最小化自由能，      *) (*   Id 层序档）的 Real 层最强可达形态 = 第三档逐 eps：                 *)
(*     ∀eps>0,  F[p_b] ≤ F[p] + D·eps。                                *) (*   本件为纯组装件：三档全链逐 eps 完成，零新数学内容。                *)
(* 【组装链结构图（各步引用件名）】                                     *) (*   第 1 步 完整分解：F[p] ≡ F[p_b] + D·Σkl_term（real_eq 载体）       *)
(*     = UpReqFEPCanon.real_kl_decomp_full_canon（主件；X2 结果）        *) (*       / real_kl_decomp_full_canon_partition（分件；Hpart 消解形）     *)
(*     载体实例化：sumf := fun f => real_list_sum X f l；               *) (*     载体代数三件 = S08_RealMainlineDPO                              *)
(*       real_list_sum_ext / real_list_sum_add / real_list_sum_linear   *) (*       （Section RealListSumMain 节泛化，X 显式首参）。               *)
(*   第 2 步 非负肢（第三档逐 eps 形）：0 ≤ Σkl_term + eps              *) (*     = S08_RealMainlineDPO.real_gibbs_inequality_eps（L490；          *)
(*       list 载体全链，Hnormp/Hnormb 双归一化前提）。                  *) (*   第 3 步 D>0 消去：0 ≤ KL+eps ∧ 0<D ⟹ 0 ≤ D·KL + D·eps             *)
(*     = S09_EntropyReal.real_le_mult_compat_r（全局形，检验实测无节     *) (*       变量泄漏）+ real_mult_zero / real_distrib（代数基元）          *)
(*       + RealSetoid.real_le_id_l / real_le_id_r（S07 Module）。       *) (*   第 4 步 逐 eps 完成：F[p]+D·eps ≡ F[p_b]+D·(KL+eps) ≥ F[p_b]+0     *)
(*     ≡ F[p_b] = S07_RealSetoidExpLog.real_le_plus_compat（全局形）    *) (*       + S02_CauchyComplete.real_le_refl + real_plus_zero             *)
(*       / real_plus_assoc + RealSetoid.real_eq_plus_compat。           *)
(*   （第 1-4 步由通用完成机 min_free_energy_close_eps 一次组装。）     *)
(*   ①正典化分解件（X2 结果）与 ②实 Gibbs 不等式逐 eps 形（S08 在盘）   *)
(*   ③④纯序代数消去/完成（S09/S07/S02 在盘）；本件增量 = 载体实例化     *)
(*   （抽象 sumf ↝ list 具体载体）+ D 因子逐字保留的序档拼装。          *)
(*   分件把 Hnormb 经 rfep_boltzmann_normalized_real（UpReqRealFEP      *)
(*   L331）消解为 partition 条件（Σ exp(−e/D) ≡ Z），与 X2 分件同型。   *)
(*   前提全显式：p 逐点正 + 双归一化（或 partition 条件）+ eps 正。     *)
(* 【红线】Set 层零 Prop（real_le/real_lt/real_eq 全 Set 值）；全 Qed   *)
(*   闭合；禁词条目零命中（头注以中文转述）；real_eq 非 Id 禁改写，      *)
(*   全链 real_eq_trans/RealSetoid 运输（运输纪律）。                  *)
(*   禁改红线：UpReqFEPCanon.v / UpReqRealFEP.v / S08 模块全程只读。     *)
(* 编译配方：_t7_run.ps1 单一入口（既有先例）+ cpu_guard CoreN 2    *)
(*   前置 .vo 全在 D:/ComplexAnalysis/ConstructiveWorld-Main/           *)
(*   ConstructiveWorld_vo/（vo 树编译，上游件零重编）。                 *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqRealFEP.
Require Import UpReqFEPCanon.

(* ---------------------------------------------------------- *)
(* 第 0 步：通用逐 eps 完成机（组装链第 3+4 步，序代数纯拼装）          *)
(*   0 < eps ∧ F[p] ≡ F[p_b] + D·KL ∧ 0 ≤ KL + eps ⟹                  *)
(*   F[p_b] ≤ F[p] + D·eps。                                            *)
(*   证明：0 ≤ KL+eps 经 D>0 放缩得 0 ≤ D·KL + D·eps；再把 F[p]+D·eps   *)
(*   沿分解恒等式运输到 F[p_b]+D·(KL+eps)，加法保序后去零项。           *)
(* ---------------------------------------------------------- *)

Lemma min_free_energy_close_eps :
  forall (D KLsum Fp Fb eps : Real),
  real_lt real_zero D ->
  real_lt real_zero eps ->
  real_eq Fp (real_plus Fb (real_mult D KLsum)) ->
  real_le real_zero (real_plus KLsum eps) ->
  real_le Fb (real_plus Fp (real_mult D eps)).
Proof.
  intros D KLsum Fp Fb eps D_pos Heps Hdec Hgibbs.
  (* 第 3 步：D>0 消去（先 lt→le 弱化桥，S09 real_r_pow_nonneg 同惯形） *)
  assert (Hdle : real_le real_zero D).
  { apply (RealSetoid.real_lt_le_iff_req real_zero D). left. exact D_pos. }
  assert (Hm0 : real_le (real_mult D real_zero)
                        (real_mult D (real_plus KLsum eps))).
  { exact (real_le_mult_compat_r D real_zero (real_plus KLsum eps)
             Hdle Hgibbs). }
  assert (Hm1 : real_le real_zero (real_mult D (real_plus KLsum eps))).
  { exact (RealSetoid.real_le_id_l real_zero (real_mult D real_zero)
             (real_mult D (real_plus KLsum eps))
             (real_eq_sym (real_mult D real_zero) real_zero
                (real_mult_zero D)) Hm0). }
  assert (Hscale : real_le real_zero
                     (real_plus (real_mult D KLsum) (real_mult D eps))).
  { exact (RealSetoid.real_le_id_r real_zero
             (real_mult D (real_plus KLsum eps))
             (real_plus (real_mult D KLsum) (real_mult D eps))
             (real_distrib D KLsum eps) Hm1). }
  (* 第 4 步：逐 eps 完成 *)
  apply (RealSetoid.real_le_id_r Fb
           (real_plus Fb (real_plus (real_mult D KLsum) (real_mult D eps)))
           (real_plus Fp (real_mult D eps))).
  - (* 等值面：F[p_b]+D·(KL+eps) ≡ F[p]+D·eps（沿分解恒等式两步运输） *)
    apply (real_eq_trans
             (real_plus Fb (real_plus (real_mult D KLsum) (real_mult D eps)))
             (real_plus (real_plus Fb (real_mult D KLsum)) (real_mult D eps))
             (real_plus Fp (real_mult D eps))).
    + exact (real_plus_assoc Fb (real_mult D KLsum) (real_mult D eps)).
    + exact (real_eq_sym (real_plus Fp (real_mult D eps))
               (real_plus (real_plus Fb (real_mult D KLsum))
                          (real_mult D eps))
               (RealSetoid.real_eq_plus_compat Fp (real_mult D eps)
                  (real_plus Fb (real_mult D KLsum)) (real_mult D eps)
                  Hdec (real_eq_refl (real_mult D eps)))).
  - (* 序面：F[p_b] ≤ F[p_b]+(D·KL+D·eps)（自反 + 加法保序 + 去零） *)
    apply (RealSetoid.real_le_id_l Fb (real_plus Fb real_zero)
             (real_plus Fb (real_plus (real_mult D KLsum) (real_mult D eps)))
             (real_eq_sym (real_plus Fb real_zero) Fb
                (real_plus_zero Fb))).
    exact (real_le_plus_compat Fb Fb real_zero
             (real_plus (real_mult D KLsum) (real_mult D eps))
             (real_le_refl Fb) Hscale).
Qed.

(* ---------------------------------------------------------- *)
(* 主件：min_free_energy_is_boltzmann_eps（定理 4.4 Real 层第三档）      *)
(*   载体 = list X 具体状态空间；前提全显式：                           *)
(*     Hnormp（Σp ≡ 1）+ Hnormb（Σp_b ≡ 1，由使用方或分件供给）。        *)
(*   组装：第 1 步喂 real_kl_decomp_full_canon（X2 正典件，sumf 实例化   *)
(*   到 real_list_sum 三件套），第 2 步喂 real_gibbs_inequality_eps。    *)
(* ---------------------------------------------------------- *)

Theorem min_free_energy_is_boltzmann_eps :
  forall (X : Type) (l : list X) (real_base_loss : X -> Real)
    (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (real_list_sum X p l) real_one ->
  real_eq
    (real_list_sum X
       (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
       l) real_one ->
  forall eps : Real,
  real_lt real_zero eps ->
  real_le
    (real_free_energy X (fun f : X -> Real => real_list_sum X f l)
       real_base_loss D
       (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
       (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r
          Z_align_r_pos))
    (real_plus
       (real_free_energy X (fun f : X -> Real => real_list_sum X f l)
          real_base_loss D p Hp)
       (real_mult D eps)).
Proof.
  intros X l real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp
         Hnormb eps Heps.
  apply (min_free_energy_close_eps D
           (real_list_sum X
              (fun s : X =>
                 real_kl_term (p s)
                   (real_boltzmann_dist_r X real_base_loss D D_pos
                      Z_align_r Z_align_r_pos s)
                   (Hp s)
                   (real_boltzmann_dist_r_pos X real_base_loss D D_pos
                      Z_align_r Z_align_r_pos s))
              l)
           (real_free_energy X (fun f : X -> Real => real_list_sum X f l)
              real_base_loss D p Hp)
           (real_free_energy X (fun f : X -> Real => real_list_sum X f l)
              real_base_loss D
              (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r
                 Z_align_r_pos)
              (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r
                 Z_align_r_pos))
           eps D_pos Heps).
  - (* 第 1 步：完整分解（X2 正典件实例化到 list 载体） *)
    exact (real_kl_decomp_full_canon X
             (fun f : X -> Real => real_list_sum X f l)
             (fun (f g : X -> Real)
                  (Hfg : forall s : X, real_eq (f s) (g s)) =>
                real_list_sum_ext X f g l Hfg)
             (fun f g : X -> Real => real_list_sum_add X f g l)
             (fun (a : Real) (f : X -> Real) =>
                real_list_sum_linear X a f l)
             real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp
             Hnormp Hnormb).
  - (* 第 2 步：实 Gibbs 不等式逐 eps 形（S08 L490 在盘） *)
    exact (real_gibbs_inequality_eps X l p
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r
                Z_align_r_pos)
             Hp
             (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r
                Z_align_r_pos)
             Hnormp Hnormb eps Heps).
Qed.

(* ---------------------------------------------------------- *)
(* 分件：min_free_energy_is_boltzmann_eps_partition（前提消解小链版）    *)
(*   与主件同结论面；Hnormb 换为 partition 条件 Hpart（Σ exp(−e/D) ≡ Z） *)
(*   ——Hnormb 经 rfep_boltzmann_normalized_real（UpReqRealFEP L331）     *)
(*   一步消解，与 X2 分件同型；Gibbs 肢照常使用。                       *)
(* ---------------------------------------------------------- *)

Theorem min_free_energy_is_boltzmann_eps_partition :
  forall (X : Type) (l : list X) (real_base_loss : X -> Real)
    (D : Real) (D_pos : real_lt real_zero D)
    (Z_align_r : Real) (Z_align_r_pos : real_lt real_zero Z_align_r)
    (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s)),
  real_eq (real_list_sum X p l) real_one ->
  real_eq
    (real_list_sum X
       (fun s : X =>
          real_exp_neg (real_mult (real_inv_pos D D_pos) (real_base_loss s)))
       l) Z_align_r ->
  forall eps : Real,
  real_lt real_zero eps ->
  real_le
    (real_free_energy X (fun f : X -> Real => real_list_sum X f l)
       real_base_loss D
       (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r Z_align_r_pos)
       (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r
          Z_align_r_pos))
    (real_plus
       (real_free_energy X (fun f : X -> Real => real_list_sum X f l)
          real_base_loss D p Hp)
       (real_mult D eps)).
Proof.
  intros X l real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp Hnormp
         Hpart eps Heps.
  assert (Hnormb : real_eq
                     (real_list_sum X
                        (real_boltzmann_dist_r X real_base_loss D D_pos
                           Z_align_r Z_align_r_pos) l) real_one).
  { exact (rfep_boltzmann_normalized_real X
             (fun f : X -> Real => real_list_sum X f l)
             (fun (f g : X -> Real)
                  (Hfg : forall s : X, real_eq (f s) (g s)) =>
                real_list_sum_ext X f g l Hfg)
             (fun (a : Real) (f : X -> Real) =>
                real_list_sum_linear X a f l)
             real_base_loss D D_pos Z_align_r Z_align_r_pos Hpart). }
  apply (min_free_energy_close_eps D
           (real_list_sum X
              (fun s : X =>
                 real_kl_term (p s)
                   (real_boltzmann_dist_r X real_base_loss D D_pos
                      Z_align_r Z_align_r_pos s)
                   (Hp s)
                   (real_boltzmann_dist_r_pos X real_base_loss D D_pos
                      Z_align_r Z_align_r_pos s))
              l)
           (real_free_energy X (fun f : X -> Real => real_list_sum X f l)
              real_base_loss D p Hp)
           (real_free_energy X (fun f : X -> Real => real_list_sum X f l)
              real_base_loss D
              (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r
                 Z_align_r_pos)
              (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r
                 Z_align_r_pos))
           eps D_pos Heps).
  - exact (real_kl_decomp_full_canon_partition X
             (fun f : X -> Real => real_list_sum X f l)
             (fun (f g : X -> Real)
                  (Hfg : forall s : X, real_eq (f s) (g s)) =>
                real_list_sum_ext X f g l Hfg)
             (fun f g : X -> Real => real_list_sum_add X f g l)
             (fun (a : Real) (f : X -> Real) =>
                real_list_sum_linear X a f l)
             real_base_loss D D_pos Z_align_r Z_align_r_pos p Hp
             Hnormp Hpart).
  - exact (real_gibbs_inequality_eps X l p
             (real_boltzmann_dist_r X real_base_loss D D_pos Z_align_r
                Z_align_r_pos)
             Hp
             (real_boltzmann_dist_r_pos X real_base_loss D D_pos Z_align_r
                Z_align_r_pos)
             Hnormp Hnormb eps Heps).
Qed.
