(* 五字段指针｜使命：本件定理／引理声明面所述性质的形式化。 依赖：件内 Require 声明面所列库件。 构造性：零承认式语句（机械核验）。 编译配方：coqc -native-compiler no -q -Q . ""。  ============================================================ *)
(* ToyR 玩具证替换件 ——   工程（tier2 第五批）        *)
(* 本件为消融落件：原件全文逐字保留，仅将文末清单所列定理之证明体  *)
(* 替换为玩具证（实质非平凡三口径：定义层受控展开／显式见证直取／  *)
(* 结构性重演，直取既勘引擎位），声明面与引用面零改动，零新增      *)
(* Require，证明结尾记号与原件逐件守恒，纯构造性闭合，文尾保留    *)
(* 原件 Print Assumptions 追印面。清单：                          *)
(*   slc_gain_ge_kl_minus_eps（原 L261，2 句玩具证）                      *)
(*   slc_gain_kl_two_sided_eps（原 L235，2 句玩具证）                     *)
(*   slc_plus_comm_r_shift（原 L101，2 句玩具证）                         *)
(*   slc_plus_r_assoc_cancel（原 L79，2 句玩具证）                        *)
(*   slc_minus_r_plus_cancel（原 L50，2 句玩具证）                        *)
(* ============================================================ *)
(* ============================================================ *)
(* 【 恒等守恒修订注记】 包AV六 （头注修订试点件） *)
(* 上方 ToyR 头注所记「仅将文末清单所列定理之证明体替换为玩具证」，   *)
(* 经 （包AL）全量恒等核查已证结论、（包AV）抽验复核：本件实测   *)
(* 为恒等守恒——清单所列 5 槽证明体与 Main 现版原件逐字同文（刀体  *)
(* ＝原体，零变化），头注「替换」声称与实物不符，特此修订。          *)
(* 修订口径：真替换 0 槽＋恒等守恒 5 槽；本注记为追加块，上方原头  *)
(* 注一字未改（历史证据保全）；证明体、声明面、语句面、Require 面   *)
(* 零改动；记录册承载见  附录／ 修正块／ 评估册。         *)
(* 附记： 判级全文恒等  *)
(* ============================================================ *)

(* ===================================================================== *)
(* SecondLawConsume.v —— 位 P6D（组 E-STAGING-P6D）：论文6 §7 第二定律  *)
(*   的依存定理推导——从核心定理 real_entropy_deficit_kl_temp              *)
(*   （S[p_T] − S[p] == KL(p‖p_T)，UpReqEntropyDeficitTemp 主件）出发，    *)
(*   依存 SecondLawQuantified（C10 ）定量出口，导出四件新结论回喂基座。   *)
(* --------------------------------------------------------------------- *)
(* 【依存链（只读依存，零基座改动）】                                      *)
(*   · real_entropy_deficit_kl_temp（13 参核心定理，检验 Check 实测）      *)
(*   · slq_entropy_gain_kl_lower（15 参）：KL − 熵增 ≤ eps（逐 eps 下界）  *)
(*   · slq_entropy_gain_kl_upper（15 参）：熵增 − KL ≤ eps（互补向）       *)
(*   · slq_second_law_eps_list（list 机器全闭形）：S[p] ≤ S[p_T] + eps     *)
(* --------------------------------------------------------------------- *)
(* 【交付四定理（slc_ 前缀防撞，全库 grep 零命中  实测）】        *)
(*   · slc_gain_kl_two_sided_eps：per-eps 双边定量（Set 层 slc_band 对；   *)
(*     下界+上界同时依存，KL ≤ 增+eps 与 增 ≤ KL+eps 合成带状）            *)
(*   · slc_gain_ge_kl_minus_eps：熵增益 ≥ KL 缺陷 − eps 的显式形           *)
(*     （real_le (KL − eps) 增；lower 经 plus 形再平移的扩展依存）          *)
(*   · slc_kl_boltz_self_zero：均衡点 p := p_T 处核心定理实例化 ⟹          *)
(*     KL(p_T‖p_T) == 0（list 机器全闭；核心定理对基座依存位回喂）          *)
(*   · slc_second_law_kl_floor_eps_list：Second Law eps 档 × 核心恒等式    *)
(*     合流 ⟹ KL(p‖p_T) ≥ −eps（list 机器全闭的双依存下限件）             *)
(* --------------------------------------------------------------------- *)
(* 【红线自审】纯构造性；结论面全 Set 层（real_eq/real_le/slc_band，        *)
(*   real_le := Or lt eq 为 Set 型 sum）；前提位照供体对位不弱化不加码；    *)
(*   全 Qed 闭合；零新承认件；禁词面静态零命中（文末 PA×4 留痕）。           *)
(* 编译配方（vorebuild 基座 + 私槽侧编 SLQ/TSI，基座零改）：                *)
(*   rocq c -Q Live/vorebuild "" -Q /tmp/p6d_side "" -Q . ""               *)
(*     SecondLawConsume.v                                                 *)
(*   （vo_901 基座   全链重编中 S01_BaseRing 已换，  *)
(*    CW_ConstructiveWorld_219.vo 尚未刷 → 假设不一致；vorebuild 链经       *)
(*    检验实测与当前 stdlib 一致，故取之。SLQ/TSI 侧编 /tmp/p6d_side，      *)
(*    EXIT=0 且 Print Assumptions 全 Closed。）                            *)
(* ===================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import SecondLawQuantified.

(* ---------------------------------------------------------- *)
(* 件 0：Set 层带状对（双边定量语句面；set 层 inductive，零 Prop）  *)
(* ---------------------------------------------------------- *)
Inductive slc_band (A B : Set) : Set :=
| slc_band_intro : A -> B -> slc_band A B.

(* ---------------------------------------------------------- *)
(* 件 1–3：real 算术 choreography 三辅助引理（全 real_eq 档）        *)
(*   (a−b)+b == a ／ (a+b)+(−b) == a ＋ (x+y)+(−z) == (x+(−z))+y  *)
(* ---------------------------------------------------------- *)
Lemma slc_minus_r_plus_cancel :
  forall a b : Real,
    real_eq (real_plus (real_minus_r a b) b) a.
Proof.
  intros a b.
  exact (real_eq_trans           (real_plus (real_minus_r a b) b)           (real_plus a (real_plus (real_opp b) b))           a           (real_eq_sym (real_plus a (real_plus (real_opp b) b))                        (real_plus (real_plus a (real_opp b)) b)                        (real_plus_assoc a (real_opp b) b))           (real_eq_trans              (real_plus a (real_plus (real_opp b) b))              (real_plus a (real_plus b (real_opp b)))              a              (RealSetoid.real_eq_plus_compat_adapt a a                 (real_plus (real_opp b) b) (real_plus b (real_opp b))                 (real_eq_refl a) (real_plus_comm (real_opp b) b))              (real_eq_trans                 (real_plus a (real_plus b (real_opp b)))                 (real_plus a real_zero)                 a                 (RealSetoid.real_eq_plus_compat_adapt a a                    (real_plus b (real_opp b)) real_zero                    (real_eq_refl a) (real_plus_opp b))                 (real_plus_zero a)))).
Qed.

Lemma slc_plus_r_assoc_cancel :
  forall a b : Real,
    real_eq (real_plus (real_plus a b) (real_opp b)) a.
Proof.
  intros a b.
  exact (real_eq_trans           (real_plus (real_plus a b) (real_opp b))           (real_plus a (real_plus b (real_opp b)))           a           (real_eq_sym (real_plus a (real_plus b (real_opp b)))                        (real_plus (real_plus a b) (real_opp b))                        (real_plus_assoc a b (real_opp b)))           (real_eq_trans              (real_plus a (real_plus b (real_opp b)))              (real_plus a real_zero)              a              (RealSetoid.real_eq_plus_compat_adapt a a                 (real_plus b (real_opp b)) real_zero                 (real_eq_refl a) (real_plus_opp b))              (real_plus_zero a))).
Qed.

Lemma slc_plus_comm_r_shift :
  forall x y z : Real,
    real_eq (real_plus (real_plus x y) (real_opp z))
            (real_plus (real_plus x (real_opp z)) y).
Proof.
  intros x y z.
  exact (real_eq_trans           (real_plus (real_plus x y) (real_opp z))           (real_plus x (real_plus y (real_opp z)))           (real_plus (real_plus x (real_opp z)) y)           (real_eq_sym (real_plus x (real_plus y (real_opp z)))                        (real_plus (real_plus x y) (real_opp z))                        (real_plus_assoc x y (real_opp z)))           (real_eq_trans              (real_plus x (real_plus y (real_opp z)))              (real_plus x (real_plus (real_opp z) y))              (real_plus (real_plus x (real_opp z)) y)              (RealSetoid.real_eq_plus_compat_adapt x x                 (real_plus y (real_opp z)) (real_plus (real_opp z) y)                 (real_eq_refl x) (real_plus_comm y (real_opp z)))              (real_plus_assoc x (real_opp z) y))).
Qed.

(* ============================================================ *)
(* 第一部分：任意和机器上的双边依存（Section 槽照 slq 同形同序）    *)
(* ============================================================ *)

Section SlcSecondLawConsume.

Variable S : Type.
Variable sumf : (S -> Real) -> Real.
Hypothesis sumpos :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (sumf f).
Hypothesis sumext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (sumf f) (sumf g).
Hypothesis sumlinear : forall (a : Real) (f : S -> Real),
  real_eq (sumf (fun s : S => real_mult a (f s))) (real_mult a (sumf f)).
Hypothesis sumadd : forall (f g : S -> Real),
  real_eq (sumf (fun s : S => real_plus (f s) (g s)))
          (real_plus (sumf f) (sumf g)).
Variable T : Real.
Hypothesis T_pos : real_lt real_zero T.
Variable energy : S -> Real.

(* 肢 1：KL ≤ 熵增 + eps（lower 之 plus 形；依存 slq_entropy_gain_kl_lower） *)
Lemma slc_kl_le_gain_plus_leg :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (sumf p) real_one ->
    real_eq (sumf (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S sumf sumpos T T_pos energy) ->
    forall eps : Real, real_lt real_zero eps ->
      real_le (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
              (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps).
Proof.
  intros p Hp Hnp Henergy eps Heps.
  pose proof (slq_entropy_gain_kl_lower S sumf sumpos sumext sumlinear sumadd
                T T_pos energy p Hp Hnp Henergy eps Heps) as Hlow.
  exact (RealSetoid.real_le_id_r
           (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
           (real_plus eps (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
           (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps)
           (real_plus_comm eps (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
           (RealSetoid.real_le_id_l
              (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
              (real_plus (real_minus_r (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                                       (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
                         (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
              (real_plus eps (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
              (real_eq_sym
                 (real_plus (real_minus_r (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                                          (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
                            (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
                 (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                 (slc_minus_r_plus_cancel
                    (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                    (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)))
              (real_le_plus_compat
                 (real_minus_r (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                               (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))
                 eps
                 (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                 (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                 Hlow
                 (real_le_refl (slq_entropy_gain S sumf sumpos T T_pos energy p Hp))))).
Qed.

(* 肢 2：熵增 ≤ KL + eps（upper 之 plus 形；依存 slq_entropy_gain_kl_upper） *)
Lemma slc_gain_le_kl_plus_leg :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (sumf p) real_one ->
    real_eq (sumf (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S sumf sumpos T T_pos energy) ->
    forall eps : Real, real_lt real_zero eps ->
      real_le (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
              (real_plus (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) eps).
Proof.
  intros p Hp Hnp Henergy eps Heps.
  pose proof (slq_entropy_gain_kl_upper S sumf sumpos sumext sumlinear sumadd
                T T_pos energy p Hp Hnp Henergy eps Heps) as Hup.
  exact (RealSetoid.real_le_id_r
           (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
           (real_plus eps (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
           (real_plus (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) eps)
           (real_plus_comm eps (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
           (RealSetoid.real_le_id_l
              (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
              (real_plus (real_minus_r (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                                       (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
                         (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
              (real_plus eps (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
              (real_eq_sym
                 (real_plus (real_minus_r (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                                          (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
                            (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
                 (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                 (slc_minus_r_plus_cancel
                    (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                    (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)))
              (real_le_plus_compat
                 (real_minus_r (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                               (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))
                 eps
                 (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                 (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                 Hup
                 (real_le_refl (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp))))).
Qed.

(* ---------------------------------------------------------- *)
(* 主件 1：per-eps 双边定量（Set 层带状对，下界+上界合并装配） *)
(*   |S[p_T] − S[p] − KL(p‖p_T)| 的逐 eps 带状读法：                *)
(*   KL ≤ 增 + eps 且 增 ≤ KL + eps。                                *)
(* ---------------------------------------------------------- *)
Theorem slc_gain_kl_two_sided_eps :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (sumf p) real_one ->
    real_eq (sumf (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S sumf sumpos T T_pos energy) ->
    forall eps : Real, real_lt real_zero eps ->
      slc_band
        (real_le (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)
                 (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps))
        (real_le (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)
                 (real_plus (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) eps)).
Proof.
  intros p Hp Hnp Henergy eps Heps.
  exact (slc_band_intro           (real_le (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)                    (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps))           (real_le (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)                    (real_plus (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) eps))           (slc_kl_le_gain_plus_leg p Hp Hnp Henergy eps Heps)           (slc_gain_le_kl_plus_leg p Hp Hnp Henergy eps Heps)).
Qed.

(* ---------------------------------------------------------- *)
(* 主件 2：熵增益 ≥ KL 缺陷 − eps（显式依存形；回喂基座依存位）      *)
(*   real_le (KL − eps) 增——lower 的 minus-r 地板形。               *)
(* ---------------------------------------------------------- *)
Theorem slc_gain_ge_kl_minus_eps :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (sumf p) real_one ->
    real_eq (sumf (fun s : S => real_mult (p s) (energy s)))
            (real_energy_exp_temp S sumf sumpos T T_pos energy) ->
    forall eps : Real, real_lt real_zero eps ->
      real_le (real_minus_r (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) eps)
              (slq_entropy_gain S sumf sumpos T T_pos energy p Hp).
Proof.
  intros p Hp Hnp Henergy eps Heps.
  exact (RealSetoid.real_le_id_r           (real_plus (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp) (real_opp eps))           (real_plus (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps)                      (real_opp eps))           (slq_entropy_gain S sumf sumpos T T_pos energy p Hp)           (slc_plus_r_assoc_cancel (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps)           (real_le_plus_compat              (slq_kl_cur_boltz S sumf sumpos T T_pos energy p Hp)              (real_plus (slq_entropy_gain S sumf sumpos T T_pos energy p Hp) eps)              (real_opp eps)              (real_opp eps)              (slc_kl_le_gain_plus_leg p Hp Hnp Henergy eps Heps)              (real_le_refl (real_opp eps)))).
Qed.

End SlcSecondLawConsume.

(* ============================================================ *)
(* 第二部分：list 机器全闭双依存（核心定理 × eps_list 依存链）       *)
(* ============================================================ *)

(* ---------------------------------------------------------- *)
(* 主件 3：均衡点 KL 归零——核心定理在 p := p_T 处实例化（全闭）      *)
(*   归一化（boltzmann_normalized）+ 同能量（E(p_T) == E_T 定义性）    *)
(*   ⟹ S[p_T] − S[p_T] == KL(p_T‖p_T) ⟹ KL(p_T‖p_T) == 0。          *)
(* ---------------------------------------------------------- *)
Theorem slc_kl_boltz_self_zero :
  forall (X : Type) (l : list X) (Hnil : l <> nil)
         (T : Real) (Ht : real_lt real_zero T) (energy : X -> Real),
    real_eq real_zero
      (slq_kl_cur_boltz X (fun g : X -> Real => real_list_sum X g l)
         (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
            real_list_sum_pos X f l Hf Hnil)
         T Ht energy
         (real_boltzmann_dist_temp X (fun g : X -> Real => real_list_sum X g l)
            (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
               real_list_sum_pos X f l Hf Hnil)
            T Ht energy)
         (real_boltzmann_dist_temp_pos X (fun g : X -> Real => real_list_sum X g l)
            (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
               real_list_sum_pos X f l Hf Hnil)
            T Ht energy)).
Proof.
  intros X l Hnil T Ht energy.
  set (SF := fun g : X -> Real => real_list_sum X g l).
  set (SP := fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
               real_list_sum_pos X f l Hf Hnil).
  set (B := real_boltzmann_dist_temp X SF SP T Ht energy).
  set (Bp := real_boltzmann_dist_temp_pos X SF SP T Ht energy).
  set (SD := real_entropy_dist X SF B Bp).
  pose proof (real_entropy_deficit_kl_temp X SF SP
                (fun f0 g0 : X -> Real => real_list_sum_ext X f0 g0 l)
                (fun (a0 : Real) (f0 : X -> Real) => real_list_sum_linear X a0 f0 l)
                (fun f0 g0 : X -> Real => real_list_sum_add X f0 g0 l)
                T Ht energy B Bp
                (real_boltzmann_dist_temp_normalized X SF SP
                   (fun f0 g0 : X -> Real => real_list_sum_ext X f0 g0 l)
                   (fun (a0 : Real) (f0 : X -> Real) => real_list_sum_linear X a0 f0 l)
                   T Ht energy)
                (real_eq_refl
                   (real_energy_exp_temp X SF SP T Ht energy))) as Hdef.
  unfold real_minus_r in Hdef.
  exact (real_eq_sym
           (real_KL_temp X SF SP T Ht energy B Bp) real_zero
           (real_eq_trans
              (real_KL_temp X SF SP T Ht energy B Bp)
              (real_plus SD (real_opp SD))
              real_zero
              (real_eq_sym (real_plus SD (real_opp SD))
                           (real_KL_temp X SF SP T Ht energy B Bp)
                           Hdef)
              (real_plus_opp SD))).
Qed.

(* ---------------------------------------------------------- *)
(* 主件 4：Second Law eps 档 × 核心恒等式合流 ⟹ KL ≥ −eps            *)
(*   依存 slq_second_law_eps_list（S[p] ≤ S[p_T]+eps）与核心定理      *)
(*   （S[p_T]−S[p] == KL）双源：0 ≤ 增+eps 沿恒等式换载 ⟹ −eps ≤ KL。 *)
(* ---------------------------------------------------------- *)
Theorem slc_second_law_kl_floor_eps_list :
  forall (X : Type) (l : list X) (Hnil : l <> nil)
         (T : Real) (Ht : real_lt real_zero T) (energy : X -> Real)
         (p : X -> Real) (Hp : forall s : X, real_lt real_zero (p s))
         (Hnp : real_eq (real_list_sum X p l) real_one)
         (Henergy : real_eq
                      (real_list_sum X (fun s : X => real_mult (p s) (energy s)) l)
                      (real_energy_exp_temp X (fun g : X -> Real => real_list_sum X g l)
                         (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                            real_list_sum_pos X f l Hf Hnil)
                         T Ht energy))
         (eps : Real) (Heps : real_lt real_zero eps),
    real_le (real_opp eps)
            (slq_kl_cur_boltz X (fun g : X -> Real => real_list_sum X g l)
               (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                  real_list_sum_pos X f l Hf Hnil)
               T Ht energy p Hp).
Proof.
  intros X l Hnil T Ht energy p Hp Hnp Henergy eps Heps.
  pose proof (slq_second_law_eps_list X l Hnil T Ht energy p Hp Hnp Henergy eps Heps) as Hsl.
  pose proof (real_entropy_deficit_kl_temp X
                (fun g : X -> Real => real_list_sum X g l)
                (fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
                   real_list_sum_pos X f l Hf Hnil)
                (fun f0 g0 : X -> Real => real_list_sum_ext X f0 g0 l)
                (fun (a0 : Real) (f0 : X -> Real) => real_list_sum_linear X a0 f0 l)
                (fun f0 g0 : X -> Real => real_list_sum_add X f0 g0 l)
                T Ht energy p Hp Hnp Henergy) as Hdef.
  set (SF := fun g : X -> Real => real_list_sum X g l) in *.
  set (SP := fun (f : X -> Real) (Hf : forall s : X, real_lt real_zero (f s)) =>
               real_list_sum_pos X f l Hf Hnil) in *.
  set (Sp := real_entropy_dist X SF p Hp) in *.
  set (Sb := real_entropy_dist X SF
               (real_boltzmann_dist_temp X SF SP T Ht energy)
               (real_boltzmann_dist_temp_pos X SF SP T Ht energy)) in *.
  set (K := real_KL_temp X SF SP T Ht energy p Hp) in *.
  (* 步 1：eps_list 加 −Sp ⟹ 0 ≤ (Sb+eps)+(−Sp) *)
  pose proof (RealSetoid.real_le_id_l real_zero
                (real_plus Sp (real_opp Sp))
                (real_plus (real_plus Sb eps) (real_opp Sp))
                (real_eq_sym (real_plus Sp (real_opp Sp)) real_zero
                             (real_plus_opp Sp))
                (real_le_plus_compat Sp (real_plus Sb eps)
                 (real_opp Sp) (real_opp Sp)
                 Hsl (real_le_refl (real_opp Sp)))) as Hstep1.
  (* 步 2：换序 ⟹ 0 ≤ (Sb+(−Sp))+eps = 0 ≤ 增+eps *)
  pose proof (RealSetoid.real_le_id_r real_zero
                (real_plus (real_plus Sb eps) (real_opp Sp))
                (real_plus (real_plus Sb (real_opp Sp)) eps)
                (slc_plus_comm_r_shift Sb eps Sp)
                Hstep1) as Hstep2.
  (* 步 3：沿核心恒等式 增 == KL 换载 ⟹ 0 ≤ KL+eps *)
  pose proof (RealSetoid.real_le_id_r real_zero
                (real_plus (real_minus_r Sb Sp) eps)
                (real_plus K eps)
                (RealSetoid.real_eq_plus_compat_adapt (real_minus_r Sb Sp) K eps eps
                   Hdef (real_eq_refl eps))
                Hstep2) as Hstep3.
  (* 步 4：加 −eps ⟹ −eps ≤ (KL+eps)+(−eps) *)
  pose proof (real_le_plus_compat real_zero (real_plus K eps)
                 (real_opp eps) (real_opp eps)
                 Hstep3 (real_le_refl (real_opp eps))) as Hstep4.
  (* 步 5：归零闭合 ⟹ −eps ≤ KL *)
  exact (RealSetoid.real_le_id_r (real_opp eps)
           (real_plus (real_plus K eps) (real_opp eps))
           K
           (slc_plus_r_assoc_cancel K eps)
           (RealSetoid.real_le_id_l (real_opp eps)
              (real_plus real_zero (real_opp eps))
              (real_plus (real_plus K eps) (real_opp eps))
              (real_eq_sym (real_plus real_zero (real_opp eps)) (real_opp eps)
                 (real_eq_trans (real_plus real_zero (real_opp eps))
                                (real_plus (real_opp eps) real_zero)
                                (real_opp eps)
                                (real_plus_comm real_zero (real_opp eps))
                                (real_plus_zero (real_opp eps))))
              Hstep4)).
Qed.

(* ===================================================================== *)
(* 审查留痕：Print Assumptions（G4）                                       *)
(* ===================================================================== *)
Print Assumptions slc_gain_kl_two_sided_eps.
Print Assumptions slc_gain_ge_kl_minus_eps.
Print Assumptions slc_kl_boltz_self_zero.
Print Assumptions slc_second_law_kl_floor_eps_list.
