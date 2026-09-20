(* ============================================================ *)
(* UpAblP6_EntropyMonoSplit_B.v —— 战役席 PA6-04（乙腿·余量枚消融），T214          *)
(*                                                              *)
(* 母本坐标：/tmp/czn14_union_full/EntropyMonoSplitInst.v（303 行，11 声明        *)
(*   = 3 Let + 3 Lemma + 1 Corollary + 4 Theorem；源副本与 Live 树同文，          *)
(*   只读消费，原树零改）。母本使命：UpReqEntropyMonoSplit.v Section              *)
(*   EmsEntropyMonoSplit 三证书槽装载件（批次 E-STAGING-CZB13，T61b C3）。         *)
(*                                                              *)
(* 双腿分工：甲腿 PA6-03（T213，施工中未落）认领语句序前三枚；本席（乙腿）         *)
(*   认领尾五枚 Qed 面——#7 emsi_kl_ge_zero_eps_mirror / #8 inst_pinned /          *)
(*   #9 inst_pinned_at_peak / #10 inst_kl_right / #11 inst_kl_left。认领集        *)
(*   与甲腿两种口径（Let 序 #1–#3 或 Qed 序 #4–#6）均零交叠，防撞车。              *)
(*                                                              *)
(* 消融口径：本件【零 Require EntropyMonoSplitInst】——母本整体摘除，               *)
(*   尾五枚逐枚自上游注册面独立重建，逐枚注明路由（实例装配 / 上游直击 /           *)
(*   独立链），禁转发冒充（转发无从谈起：原件不在依赖闭包内）。                    *)
(*   逐枚路由判词：                                                              *)
(*   A1 uab_kl_ge_zero_eps_mirror（消融 #7）——实例装配·16 参全显直喂：            *)
(*      上游种子全库唯一（real_KL_temp_ge_zero_eps，UpReqEntropyMaxTemp.v:197），  *)
(*      装配方按 E-STAGING-SigMigrate2R/ReqDist2 卡「全显式参数 exact」纪律。      *)
(*   A2 uab_inst_pinned_at_peak（消融 #9）——上游直击·零前提：real_eq_refl          *)
(*      定义性合一（uab_bt δ→real_boltzmann_dist_temp 与 real_energy_exp_temp      *)
(*      δ 展开逐字同项），绕开母本桥件一（#4 被消融亦不受累）。                    *)
(*   A3 uab_inst_pinned（消融 #8）——实例装配：real_eq_trans 自钉腿内联            *)
(*      real_eq_refl + 片运输供位 Hslice（约束内容显式隔离不藏前提），             *)
(*      trans 中项写字面（E-STAGING-GEOMB-ringatom-unify 卡 L21 纪律）。           *)
(*   A4 uab_inst_kl_right（消融 #10）——独立链：差分桥/eps 桥以新名重建             *)
(*      （uab_le_diff_ge_zero / uab_le_plus_eps），零消费母本 #5/#6；              *)
(*      其中 eps 桥换道——母本走 compat+id_l(0+0≡0) 换端，本件改走                 *)
(*      nonneg_r(0≤0+eps) + compat + real_le_trans 三段链，组合序独立。            *)
(*   A5 uab_inst_kl_left（消融 #11）——独立链：A4 桥组镜像装配（KL_u 在前，        *)
(*      禁倒置红线照抄母本）。                                                    *)
(*   差分桥（uab_le_diff_ge_zero）注记：raw Real 层注册面差分向唯一通行            *)
(*      （compat + id_l(a+(−a)≡0) 换左端），以新名重建、系独立链_aux 面非消融靶。   *)
(*                                                              *)
(* 检索记录：经验/检索索引.md 对 EntropyMonoSplit/Ems/CZB13/T61b 零卡备案          *)
(*   （索引盲区），按 E-STAGING-GEOMB-ringatom-unify（签名序实证/中项写字面）       *)
(*   与 E-STAGING-SigMigrate2R、E-STAGING-ReqDist2（全显参数 exact）三卡纪律施工。  *)
(*                                                              *)
(* 纪律：纯构造性零承认件；Set 层语句零 Prop 泄露（全 real_eq/real_lt/real_le      *)
(*   sigT-Or 形）；全件真 Qed 收口（零悬置、零假设位）；Live 树与 vo_9.1 只读，     *)
(*   .vo 只落 /tmp/pa7_work；尾嵌 Print Assumptions 五连自检段。                   *)
(* 编译配方：source Live/toolchain/env.sh 后                                      *)
(*   cd /tmp/pa7_work && rocq c -Q /tmp/pa7_work "" -Q /tmp/pa6_side ""            *)
(*     -Q /tmp/czn14_union_full "" UpAblP6_EntropyMonoSplit_B.v（9.1 live 轨）      *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpReqEntropyMaxTemp.

(* ============================================================ *)
(* Section UpAblP6EmsB：接口面照母本 Section EntropyMonoSplitInst 同名同序         *)
(*   （求和面 7 位 + 峰温 T_star + 能量）；速记件以 uab_ 前缀重建（非转发：        *)
(*   系接口重建，母本整体不在依赖闭包内）。                                        *)
(* ============================================================ *)
Section UpAblP6EmsB.

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

(* ---- 速记重建（uab_bt / uab_bt_pos / uab_kl：与母本 Let 同形换名，             *)
(*   KL 方向红线照抄：KL(p_u 竖排 p_{t*})，p_u 占第一分布位，禁倒置。） ---- *)
Let uab_bt (u : Real) (Hu : real_lt real_zero u) : S -> Real :=
  real_boltzmann_dist_temp S real_sum_over_S real_sum_pos_preserved u Hu energy.
Let uab_bt_pos (u : Real) (Hu : real_lt real_zero u) :
  forall s : S, real_lt real_zero (uab_bt u Hu s) :=
  real_boltzmann_dist_temp_pos S real_sum_over_S real_sum_pos_preserved u Hu energy.
Let uab_kl (u : Real) (Hu : real_lt real_zero u) : Real :=
  real_KL_temp S real_sum_over_S real_sum_pos_preserved T_star T_star_pos energy
               (uab_bt u Hu) (uab_bt_pos u Hu).

(* ---------------------------------------------------------- *)
(* 独立链辅助件一（差分向）：a ≤ b 给 0 ≤ b + (−a)。                              *)
(*   raw Real 层差分向唯一通行：compat 双边同加 −a，再 id_l 经                     *)
(*   (a + −a) ≡ 0 换左端。新名重建，零消费母本 #5。                                *)
(* ---------------------------------------------------------- *)
Lemma uab_le_diff_ge_zero :
  forall a b : Real,
    real_le a b -> real_le real_zero (real_plus b (real_opp a)).
Proof.
  intros a b Hab.
  exact (RealSetoid.real_le_id_l real_zero
           (real_plus a (real_opp a))
           (real_plus b (real_opp a))
           (real_eq_sym (real_plus a (real_opp a)) real_zero
              (real_plus_opp a))
           (real_le_plus_compat a b (real_opp a) (real_opp a) Hab
              (real_le_refl (real_opp a)))).
Qed.

(* ---------------------------------------------------------- *)
(* 独立链辅助件二（eps 松弛提升）：0 ≤ X 且 0 < eps 给 0 ≤ X + eps。               *)
(*   【换道注记】母本 #6 走 compat(0≤X)(0≤eps) + id_l((0+0)≡0) 换端；              *)
(*   本件组合序独立：nonneg_r（0 ≤ 0+eps）→ compat 左端 0≤X 提升                   *)
(*   （0+eps ≤ X+eps）→ real_le_trans 中项字面 (0+eps) 缝合。                      *)
(*   新名重建，零消费母本 #6。                                                    *)
(* ---------------------------------------------------------- *)
Lemma uab_le_plus_eps :
  forall X eps : Real,
    real_le real_zero X -> real_lt real_zero eps ->
    real_le real_zero (real_plus X eps).
Proof.
  intros X eps HX Heps.
  exact (real_le_trans real_zero
           (real_plus real_zero eps)
           (real_plus X eps)
           (real_le_plus_nonneg_r real_zero eps
              (real_le_from_lt_aux real_zero eps Heps))
           (real_le_plus_compat real_zero X eps eps HX
              (real_le_refl eps))).
Qed.

(* ---------------------------------------------------------- *)
(* A1（消融 #7 emsi_kl_ge_zero_eps_mirror）：镜像 exact 换装孪生。                  *)
(*   路由：实例装配·16 参全显直喂（上游种子全库唯一：                              *)
(*   real_KL_temp_ge_zero_eps，UpReqEntropyMaxTemp.v:197），                        *)
(*   10 接口位照本节同名同序换装，温度位 T := t*。                                 *)
(* ---------------------------------------------------------- *)
Theorem uab_kl_ge_zero_eps_mirror :
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
(* A2（消融 #9 inst_pinned_at_peak）：峰温点零前提封闭装载。                        *)
(*   路由：上游直击·零前提——real_eq_refl 定义性合一（uab_bt 与                    *)
(*   real_energy_exp_temp δ 展开逐字同项，kernel 可转换），母本桥件一              *)
(*   （#4）被消融亦不受累。装载体闭合性证人。                                      *)
(* ---------------------------------------------------------- *)
Theorem uab_inst_pinned_at_peak :
  real_eq
    (real_sum_over_S
       (fun s : S => real_mult (uab_bt T_star T_star_pos s) (energy s)))
    (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
       T_star T_star_pos energy).
Proof.
  exact (real_eq_refl
           (real_sum_over_S
              (fun s : S => real_mult (uab_bt T_star T_star_pos s) (energy s)))).
Qed.

(* ---------------------------------------------------------- *)
(* A3（消融 #8 inst_pinned）：槽位1 Hpinned 装载（逐字结论形）。                    *)
(*   路由：实例装配——自钉腿内联 real_eq_refl（母本桥件一 #4 被消融，               *)
(*   定义性合一零桥直达）+ 片运输供位 Hslice（E_u == E_{t*}，约束内容              *)
(*   显式隔离不藏前提），real_eq_trans 中项写字面。                                *)
(* ---------------------------------------------------------- *)
Theorem uab_inst_pinned :
  (forall (u : Real) (Hu : real_lt real_zero u),
     real_eq
       (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
          u Hu energy)
       (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
          T_star T_star_pos energy)) ->
  forall (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (real_sum_over_S (fun s : S => real_mult (uab_bt u Hu s) (energy s)))
      (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
         T_star T_star_pos energy).
Proof.
  intros Hslice u Hu.
  exact (real_eq_trans
           (real_sum_over_S
              (fun s : S => real_mult (uab_bt u Hu s) (energy s)))
           (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
              u Hu energy)
           (real_energy_exp_temp S real_sum_over_S real_sum_pos_preserved
              T_star T_star_pos energy)
           (real_eq_refl
              (real_sum_over_S
                 (fun s : S => real_mult (uab_bt u Hu s) (energy s))))
           (Hslice u Hu)).
Qed.

(* ---------------------------------------------------------- *)
(* A4（消融 #10 inst_kl_right）：槽位2 Hkl_right 装载（逐字结论形）。               *)
(*   路由：独立链——供位定型 plain growth（real_le KL_u KL_v）→ 新名                *)
(*   差分桥换装 → 新名 eps 桥（换道组合）提升。KL_v 在前 KL_u 取 real_opp，        *)
(*   禁倒置红线照抄母本。零消费母本 #5/#6/#10。                                    *)
(* ---------------------------------------------------------- *)
Theorem uab_inst_kl_right :
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le T_star u -> real_le u v ->
     real_le (uab_kl u Hu) (uab_kl v Hv)) ->
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le T_star u -> real_le u v ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus (real_plus (uab_kl v Hv) (real_opp (uab_kl u Hu))) eps).
Proof.
  intros Hgrowth u v Hu Hv Htu Huv eps Heps.
  exact (uab_le_plus_eps
           (real_plus (uab_kl v Hv) (real_opp (uab_kl u Hu))) eps
           (uab_le_diff_ge_zero (uab_kl u Hu) (uab_kl v Hv)
              (Hgrowth u v Hu Hv Htu Huv))
           Heps).
Qed.

(* ---------------------------------------------------------- *)
(* A5（消融 #11 inst_kl_left）：槽位3 Hkl_left 装载（逐字结论形）。                 *)
(*   路由：独立链——供位定型 plain decay（real_le KL_v KL_u，序前提                 *)
(*   u ≤ v ≤ t*）→ 同组新名桥镜像装配。KL_u 在前 KL_v 取 real_opp，                *)
(*   禁倒置红线照抄母本。零消费母本 #5/#6/#11。                                    *)
(* ---------------------------------------------------------- *)
Theorem uab_inst_kl_left :
  (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
     real_le u v -> real_le v T_star ->
     real_le (uab_kl v Hv) (uab_kl u Hu)) ->
  forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
    real_le u v -> real_le v T_star ->
    forall eps : Real,
      real_lt real_zero eps ->
      real_le real_zero
        (real_plus (real_plus (uab_kl u Hu) (real_opp (uab_kl v Hv))) eps).
Proof.
  intros Hdecay u v Hu Hv Huv Hvt eps Heps.
  exact (uab_le_plus_eps
           (real_plus (uab_kl u Hu) (real_opp (uab_kl v Hv))) eps
           (uab_le_diff_ge_zero (uab_kl v Hv) (uab_kl u Hu)
              (Hdecay u v Hu Hv Huv Hvt))
           Heps).
Qed.

End UpAblP6EmsB.

(* ---- G1 内嵌自检段（四关前置：文件内显式 PA 声明五连） ---- *)
Print Assumptions uab_kl_ge_zero_eps_mirror.
Print Assumptions uab_inst_pinned_at_peak.
Print Assumptions uab_inst_pinned.
Print Assumptions uab_inst_kl_right.
Print Assumptions uab_inst_kl_left.
