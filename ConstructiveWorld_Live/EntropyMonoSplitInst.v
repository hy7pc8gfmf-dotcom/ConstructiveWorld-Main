(* ============================================================ *)
(* EntropyMonoSplitInst.v —— 席位CZB13（批次 E-STAGING-CZB13）       *)
(* T61b C3：UpReqEntropyMonoSplit 三证书槽装载件                     *)
(*                                                              *)
(* 【使命】源件 ConstructiveWorld_Live/UpReqEntropyMonoSplit.v        *)
(*   Section EmsEntropyMonoSplit 三证书位（接口假设，全库无根）：      *)
(*     槽位1  Hpinned    :137 能量钉（片上 E(p_u) == E_{t*}）；       *)
(*     槽位2  Hkl_right  :146 峰右支 KL 增长证书（eps 形）；           *)
(*     槽位3  Hkl_left   :153 峰左支 KL 衰减证书（eps 形）。           *)
(*   本件为三槽各出一枚装载定理（inst_pinned / inst_kl_right /        *)
(*   inst_kl_left），另配镜像 exact 换装孪生与峰温点零前提装载，      *)
(*   逐枚附四要素核销宣言。结论面与槽语句逐字同形，零改弱。           *)
(*                                                              *)
(* 【三证书位匹配度定谳（实勘结论）】                                   *)
(*   槽位2/3 消费面：已注册镜像 real_KL_temp_ge_zero_eps                *)
(*     （UpReqEntropyMaxTemp.v:197，全库唯一注册位；出节 16 参全显）。 *)
(*     匹配度：eps 松弛形 real_le real_zero (real_plus _ eps) 逐字     *)
(*     同构，镜像供「0 ≤ KL+eps」单分布形；槽语句供「0 ≤ KL_v−KL_u+eps」 *)
(*     差分增长形——形面同构、内容面差一 growth 腿。装载路径分两层：    *)
(*     (a) 镜像 exact 换装孪生 emsi_kl_ge_zero_eps_mirror（T:=t*       *)
(*         参数换装，16 参全显直喂）；                                  *)
(*     (b) inst_kl_right/left 供位定型为 plain growth（KL-V 形文义），  *)
(*         经 emsi_le_diff_ge_zero（a ≤ b 给 0 ≤ b−a，真证新形）       *)
(*         + emsi_le_plus_eps（eps 松弛提升）两级换装提升至槽语句。     *)
(*   槽位1 消费面：GibbsAssembly（消融50/GibbsAssembly.v）实测          *)
(*     【接口面不足】：该件系 req2 增强层（RealInterfaceEnhancedSetoid） *)
(*     Gibbs 不等式组装机（ga2_gibbs_eps 系），通篇无能量钉件；且源件   *)
(*     头注【跨层红线注记】明令 Id/增强层与 raw Real 层禁混引——架桥    *)
(*     违红线，故按任务书「接口面不足先建小桥再装载」条款改消费          *)
(*     raw Real 层注册能量钉面：real_energy_exp_temp                    *)
(*     （UpReqTempDefs.v:199，定义面 = Σ p_T·e，与 4.6b 定理            *)
(*     real_max_entropy_is_boltzmann_temp_eps 的 Henergy 槽             *)
(*     UpReqEntropyMaxTemp.v:364-366 逐字同形）。小桥两件：              *)
(*     emsi_energy_pin_self（逐温自钉，定义性 real_eq_refl 真装）       *)
(*     + 片运输供位（E_u == E_{t*}，即源件「约束出现」变量显式隔离）；   *)
(*     inst_pinned 结论面保持 Hpinned 逐字形。峰温点另给零前提封闭       *)
(*     装载 inst_pinned_at_peak（u := t* 时自钉面即槽面）。             *)
(*                                                              *)
(* 【纪律】纯构造性零承认件；Set 层语句零 Prop 泄露（全 real_eq/        *)
(*   real_lt/real_le sigT-Or 形）；本件零 Hypothesis（接口位全          *)
(*   Variable，供位全显式前提参）；原树只读，自建 .vo 只留 /tmp；       *)
(*   尾嵌 Print Assumptions 自检段。                                    *)
(* 编译配方：source Live/toolchain/env.sh 后                            *)
(*   rocq c -Q <基座根> "" -Q . "" EntropyMonoSplitInst.v（9.1 live 轨） *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpReqEntropyMaxTemp.

(* ============================================================ *)
(* Section EntropyMonoSplitInst：接口面照源件 Section                   *)
(*   EmsEntropyMonoSplit 同名同序（求和面 7 位 + 峰温 T_star + 能量），  *)
(*   证书位不作 Hypothesis（本件使命即装载证书，供位走显式前提参）。     *)
(* ============================================================ *)
Section EntropyMonoSplitInst.

Variable S : Type.
Variable real_sum_over_S : (S -> Real) -> Real.
Variable real_sum_pos_preserved :
  forall (f : S -> Real),
    (forall s : S, real_lt real_zero (f s)) -> real_lt real_zero (real_sum_over_S f).
Variable real_sum_over_S_ext : forall (f g : S -> Real),
  (forall s : S, real_eq (f s) (g s)) -> real_eq (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_le : forall (f g : S -> Real),
  (forall s : S, real_le (f s) (g s)) -> real_le (real_sum_over_S f) (real_sum_over_S g).
Variable real_sum_over_S_linear : forall (a : Real) (f : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_mult a (f s)))
          (real_mult a (real_sum_over_S f)).
Variable real_sum_over_S_add : forall (f g : S -> Real),
  real_eq (real_sum_over_S (fun s : S => real_plus (f s) (g s)))
          (real_plus (real_sum_over_S f) (real_sum_over_S g)).
Variable T_star : Real.
Variable T_star_pos : real_lt real_zero T_star.
Variable energy : S -> Real.

(* ---- 速记（照源件 Let ems_bt / ems_bt_pos / ems_kl_peak 同形换名，    *)
(*   保证槽语句换装后逐字对位；KL 方向红线照抄源件：KL(p_u 竖排 p_{t*})  *)
(*   p_u 占第一分布位，p_{t*} 占参考位，禁倒置。） ---- *)
Let emsi_bt (u : Real) (Hu : real_lt real_zero u) : S -> Real :=
  real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved u Hu energy.
Let emsi_bt_pos (u : Real) (Hu : real_lt real_zero u) :
  forall s : S, real_lt real_zero (emsi_bt u Hu s) :=
  real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved u Hu energy.
Let emsi_kl (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_KL_temp S real_sum_over_S real_sum_pos_preserved T_star T_star_pos energy
               (emsi_bt u Hu) (emsi_bt_pos u Hu).

(* ---------------------------------------------------------- *)
(* 桥件一（槽位1 小桥·能量钉注册面自钉形）：逐温能量期望自钉。           *)
(*   real_energy_exp_temp 定义面即 Σ p_T·e（UpReqTempDefs.v:199），     *)
(*   左端 lambda 经 emsi_bt 换名后定义性合一，real_eq_refl 真装。        *)
(*   此形与 4.6b 定理 Henergy 槽（UpReqEntropyMaxTemp.v:364-366）       *)
(*   逐字同形（T := u 任意正温）。                                       *)
(* ---------------------------------------------------------- *)
Lemma emsi_energy_pin_self :
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (real_sum_over_S (fun s : S => real_mult (emsi_bt u Hu s) (energy s)))
      (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
         u Hu energy).
Proof.
  intros u Hu.
  exact (real_eq_refl
           (real_sum_over_S
              (fun s : S => real_mult (emsi_bt u Hu s) (energy s)))).
Qed.

(* ---------------------------------------------------------- *)
(* 桥件二（序代数·差分非负新形）：a ≤ b 给 0 ≤ b − a。                   *)
(*   raw Real 层注册面只有反方向工作马 real_le_plus_nonneg_r             *)
(*   （0 ≤ b 给 a ≤ a+b，UpReqEntropyMaxTemp.v:79）；本件补齐差分向：    *)
(*   real_le_plus_compat 双边同加 −a，再 RealSetoid.real_le_id_l         *)
(*   经 (a + −a) ≡ 0 换左端。纯项模式真证。                              *)
(* ---------------------------------------------------------- *)
Lemma emsi_le_diff_ge_zero :
  forall a b : Real,
    real_le a b -> real_le real_zero (real_plus b (real_opp a)).
Proof.
  intros a b Hab.
  apply (RealSetoid.real_le_id_l real_zero
           (real_plus a (real_opp a))
           (real_plus b (real_opp a))
           (real_eq_sym (real_plus a (real_opp a)) real_zero
              (real_plus_opp a))).
  exact (real_le_plus_compat a b (real_opp a) (real_opp a) Hab
           (real_le_refl (real_opp a))).
Qed.

(* ---------------------------------------------------------- *)
(* 桥件三（eps 松弛提升形）：0 ≤ X 且 0 < eps 给 0 ≤ X + eps。           *)
(*   镜像族「0 ≤ KL+eps 形」的序代数内核：compat 双边加 eps，           *)
(*   左端 (0+0) ≡ 0 换装。                                              *)
(* ---------------------------------------------------------- *)
Lemma emsi_le_plus_eps :
  forall X eps : Real,
    real_le real_zero X -> real_lt real_zero eps ->
    real_le real_zero (real_plus X eps).
Proof.
  intros X eps HX Heps.
  apply (RealSetoid.real_le_id_l real_zero
           (real_plus real_zero real_zero)
           (real_plus X eps)
           (real_eq_sym (real_plus real_zero real_zero) real_zero
              (real_plus_zero real_zero))).
  exact (real_le_plus_compat real_zero X real_zero eps HX
           (real_le_from_lt_aux real_zero eps Heps)).
Qed.

(* ---------------------------------------------------------- *)
(* 镜像 exact 换装孪生（槽位2/3 词料种子）：                              *)
(*   已注册镜像 real_KL_temp_ge_zero_eps（UpReqEntropyMaxTemp.v:197，    *)
(*   全库唯一注册位）16 参全显直喂，温度位换装 T := t*。                 *)
(*   四要素核销宣言：                                                    *)
(*   · 槽位坐标：源件 :142-144 头注自注「镜像已注册」词料位；            *)
(*   · 原语义：0 ≤ KL(p 竖排 p_{t*}) + eps（归一 + 逐点正 + eps 正）；   *)
(*   · 装载路径：出节镜像 16 参全显应用，10 接口位照本节同名同序换装；   *)
(*   · 定理引用：real_KL_temp_ge_zero_eps（UpReqEntropyMaxTemp.v:197）。 *)
(* ---------------------------------------------------------- *)
Corollary emsi_kl_ge_zero_eps_mirror :
  forall (p : S -> Real) (Hp : forall s : S, real_lt real_zero (p s)),
    real_eq (real_sum_over_S p) real_one ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus
           (real_KL_temp S real_sum_over_S real_sum_pos_preserved
              T_star T_star_pos energy p Hp)
           eps).
Proof.
  intros p Hp Hnp eps Heps.
  exact (real_KL_temp_ge_zero_eps
           S real_sum_over_S real_sum_pos_preserved
           real_sum_over_S_ext real_sum_over_S_le real_sum_over_S_linear
           real_sum_over_S_add
           T_star T_star_pos energy p Hp Hnp eps Heps).
Qed.

(* ---------------------------------------------------------- *)
(* 装载定理一（槽位1 Hpinned，源件 :137-140 逐字结论形）。               *)
(*   四要素核销宣言：                                                    *)
(*   · 槽位坐标：UpReqEntropyMonoSplit.v:137（Hpinned 能量钉）；          *)
(*   · 原语义：约束片上 E(p_u) == E_{t*} 对一切正温 u（C5「约束出现」   *)
(*     变量的定理化载体）；                                              *)
(*   · 装载路径：GibbsAssembly 判接口面不足（req2 增强层无能量钉件 +     *)
(*     源件层红线禁混引），改走 raw Real 层注册面小桥：emsi_energy_pin_  *)
(*     self（自钉，定义性）经 real_eq_trans 复合片运输供位               *)
(*     （E_u == E_{t*}，约束内容显式隔离，不藏前提）；                   *)
(*   · 定理引用：real_energy_exp_temp（UpReqTempDefs.v:199 定义面；      *)
(*     Henergy 槽同形 UpReqEntropyMaxTemp.v:364）。                      *)
(* ---------------------------------------------------------- *)
Theorem inst_pinned :
  (forall (u : Real) (Hu : real_lt real_zero u),
     real_eq
       (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
          u Hu energy)
       (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
          T_star T_star_pos energy)) ->
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (real_sum_over_S (fun s : S => real_mult (emsi_bt u Hu s) (energy s)))
      (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
         T_star T_star_pos energy).
Proof.
  intros Hslice u Hu.
  exact (real_eq_trans
           (real_sum_over_S
              (fun s : S => real_mult (emsi_bt u Hu s) (energy s)))
           (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
              u Hu energy)
           (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
              T_star T_star_pos energy)
           (emsi_energy_pin_self u Hu)
           (Hslice u Hu)).
Qed.

(* ---------------------------------------------------------- *)
(* 装载定理一孪生（峰温点零前提封闭装载）：u := t* 时片运输供位退化      *)
(*   为自反，槽面即自钉面——零供位真装（装载体闭合性证人）。              *)
(* ---------------------------------------------------------- *)
Theorem inst_pinned_at_peak :
  real_eq
    (real_sum_over_S
       (fun s : S => real_mult (emsi_bt T_star T_star_pos s) (energy s)))
    (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
       T_star T_star_pos energy).
Proof.
  exact (emsi_energy_pin_self T_star T_star_pos).
Qed.

(* ---------------------------------------------------------- *)
(* 装载定理二（槽位2 Hkl_right，源件 :146-152 逐字结论形）。             *)
(*   四要素核销宣言：                                                    *)
(*   · 槽位坐标：UpReqEntropyMonoSplit.v:146（Hkl_right 峰右支）；        *)
(*   · 原语义：0 ≤ KL_v − KL_u + eps（t* ≤ u ≤ v，「KL 随温增」读向，   *)
(*     KL_v 在前 KL_u 取 real_opp，禁倒置）；                            *)
(*   · 装载路径：供位定型 plain growth（KL-V 形右支文义 real_le KL_u     *)
(*     KL_v）→ emsi_le_diff_ge_zero 差分换装 → emsi_le_plus_eps          *)
(*     eps 松弛提升；词料面由镜像换装孪生备案（eps 形同构）；            *)
(*   · 定理引用：real_KL_temp_ge_zero_eps（镜像孪生                      *)
(*     emsi_kl_ge_zero_eps_mirror 消费位）+ emsi 两级换装桥。            *)
(* ---------------------------------------------------------- *)
Theorem inst_kl_right :
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le T_star u -> real_le u v ->
     real_le (emsi_kl u Hu) (emsi_kl v Hv)) ->
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le T_star u -> real_le u v ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus (real_plus (emsi_kl v Hv) (real_opp (emsi_kl u Hu))) eps).
Proof.
  intros Hgrowth u v Hu Hv Htu Huv eps Heps.
  exact (emsi_le_plus_eps
           (real_plus (emsi_kl v Hv) (real_opp (emsi_kl u Hu))) eps
           (emsi_le_diff_ge_zero (emsi_kl u Hu) (emsi_kl v Hv)
              (Hgrowth u v Hu Hv Htu Huv))
           Heps).
Qed.

(* ---------------------------------------------------------- *)
(* 装载定理三（槽位3 Hkl_left，源件 :153-159 逐字结论形）。              *)
(*   四要素核销宣言：                                                    *)
(*   · 槽位坐标：UpReqEntropyMonoSplit.v:153（Hkl_left 峰左支）；          *)
(*   · 原语义：0 ≤ KL_u − KL_v + eps（u ≤ v ≤ t*，「KL 向峰衰减」       *)
(*     读向，镜像右支，禁倒置）；                                        *)
(*   · 装载路径：供位定型 plain decay（real_le KL_v KL_u，序前提         *)
(*     u ≤ v ≤ t*）→ 同一枚差分桥 + eps 松弛桥两级换装；                 *)
(*   · 定理引用：同槽位2（镜像孪生 + emsi 换装桥）。                     *)
(* ---------------------------------------------------------- *)
Theorem inst_kl_left :
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le u v -> real_le v T_star ->
     real_le (emsi_kl v Hv) (emsi_kl u Hu)) ->
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le u v -> real_le v T_star ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus (real_plus (emsi_kl u Hu) (real_opp (emsi_kl v Hv))) eps).
Proof.
  intros Hdecay u v Hu Hv Huv Hvt eps Heps.
  exact (emsi_le_plus_eps
           (real_plus (emsi_kl u Hu) (real_opp (emsi_kl v Hv))) eps
           (emsi_le_diff_ge_zero (emsi_kl v Hv) (emsi_kl u Hu)
              (Hdecay u v Hu Hv Huv Hvt))
           Heps).
Qed.

End EntropyMonoSplitInst.

(* ---- G1 内嵌自检段（四关前置：文件内显式 PA 声明） ---- *)
Print Assumptions emsi_energy_pin_self.
Print Assumptions emsi_le_diff_ge_zero.
Print Assumptions emsi_le_plus_eps.
Print Assumptions emsi_kl_ge_zero_eps_mirror.
Print Assumptions inst_pinned.
Print Assumptions inst_pinned_at_peak.
Print Assumptions inst_kl_right.
Print Assumptions inst_kl_left.
