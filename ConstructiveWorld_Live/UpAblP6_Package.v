(* ===================================================================== *)
(* UpAblP6_Package.v —— T221b / PA6-13 席（论文6 消融战役合龙旗舰件）      *)
(*                                                                       *)
(* 使命：七件战役件（GibbsFamilyExt 5 / TempDefs 11 / EntropyMonoSplit_A 6 *)
(*   / _B 7 / S5SlotWire 11 / ZPosLowRef 12 / ConcMixSelFeed 16，合计      *)
(*   68 Qed）Require 合龙，四面总装 14 枚真 Qed（前缀 uapkg6_）：           *)
(*   a 温度族×槽位面整合：Gibbs 温度实例（β=1/β=2）＋TempDefs 槽供给        *)
(*      →「温度参数化全供给」总装句（uapkg6_temp_param_full_supply）。      *)
(*   b EntropyMonoSplit 覆盖总装：A+B 两件对母件 EntropyMonoSplitInst       *)
(*      11 枚的覆盖——速记位 3 枚（#1 bt/#2 bt_pos/#3 kl 重建位，其证书面    *)
(*      经 #7–#11 出节形消费，此处以速记位正性件作覆盖证人）＋定理面        *)
(*      8 枚逐枚一行 Corollary，另以打包 completeness 句收口。              *)
(*   c 喂件族整合：S5SlotWire＋ZPosLowRef＋ConcMixSelFeed 三喂件面的        *)
(*      代表性实例总装句（抽象接口面 + 具体实例面两件）。                   *)
(*   d 战役总装 Corollary：论文6 五独占模块（GibbsFamilyExt / TempDefs /     *)
(*      FepIdConsume 零槽 / EntropyMonoSplitInst / 喂件族）假设供给闭合     *)
(*      的一揽子陈述，每支引对应件真证（uapkg6_campaign_supply_closed）。   *)
(*                                                                       *)
(* 纪律：七件本体零改（只 Require）；传递 Require 不 Import 不透传，依赖    *)
(*   面逐一显式点名；双根 -Q /tmp/pa7_work "" 挂首防同名歧义；14 枚全真 Qed *)
(*   非转发（每枚自带语句与证明，消费上游件出节形经转换收口）；全件语句面   *)
(*   为 CW219 Set 值层（real_lt/real_eq/real_le_b 等 Set 值），Set 层合取   *)
(*   一律 sigT 打包（P7 坑卡⑤），禁 Prop conj 混装；纯构造性、零公理零承   *)
(*   认；.vo 只落 /tmp/pa7_work；尾嵌 Print Assumptions 十四连自检。        *)
(* ===================================================================== *)

(* ---------- 依赖面（显式点名；⑨：Import 载荷不透传） ---------- *)
Require Import CW_ConstructiveWorld_219.
Require Import S01_BaseRing.
Require Import UpRealLeB.
Require Import UpReqKLStrictB.
Require Import UpReqTempDefs.
Require Import UpReqEntropyDeficitTemp.
Require Import UpReqSumD.
Require Import UpReqAttnGibbs.
Require Import UpReqConcSoftmax.
Require Import fa56_id_carrier.
Require Import fa56c_ext.
Require Import p4a_GradSignQDec.
Require Import FepIdentClass.
Require Import S07_RealSetoidExpLog.
From Stdlib Require Import QArith_base Qring Qabs.
Import RealInterfaceEnhancedMod.

(* ---------- 七件战役件（显式 Require；本席辖区 T221b） ---------- *)
Require Import UpAblP6_GibbsFamilyExt.
Require Import UpAblP6_TempDefs.
Require Import UpAblP6_EntropyMonoSplit_A.
Require Import UpAblP6_EntropyMonoSplit_B.
Require Import UpAblP6_S5SlotWire.
Require Import UpAblP6_ZPosLowRef.
Require Import UpAblP6_ConcMixSelFeed.

(* 论文6 母件：FepIdConsume（零槽面，d 支引用） *)
Require Import FepIdConsume.

(* ===================================================================== *)
(* a 面：温度族×槽位面整合——「温度参数化全供给」总装句                     *)
(*   TempDefs 出节形：uap6t_* 于任意正温 T、任意能量 energy 上全槽供给；    *)
(*   GibbsFamilyExt 温度实例两枚（β=1 单位温度 le_b 形 / β=2 双倍温度       *)
(*   eps 弱前提形）挂接同一温度参数轴——七支 sigT 打包，逐支引对应件真证。  *)
(* ===================================================================== *)
Theorem uapkg6_temp_param_full_supply :
  forall (T : Real) (T_pos : real_lt real_zero T) (energy : unit -> Real),
    {_ : (forall s : unit, real_lt real_zero (uap6t_bf T T_pos energy s)) &
     {_ : real_lt real_zero (uap6t_Z T T_pos energy) &
     {_ : (forall s : unit, real_lt real_zero (uap6t_dist T T_pos energy s)) &
     {_ : real_eq (uap6t_sum1 (uap6t_dist T T_pos energy)) real_one &
     {_ : real_eq (uap6t_entropy_dist (uap6t_dist T T_pos energy)
                     (uap6t_dist_pos T T_pos energy))
                  (real_plus
                     (real_mult (real_inv_pos T T_pos)
                                (uap6t_energy_exp T T_pos energy))
                     (real_log (uap6t_Z T T_pos energy)
                               (uap6t_Z_pos T T_pos energy))) &
     {_ : (forall (p q : Real) (Hp : real_lt real_zero p)
                  (Hq : real_lt real_zero q),
             real_le_b (real_mult real_one (real_plus p (real_opp q)))
                       (real_mult real_one (real_kl_term p q Hp Hq))) &
          (forall (p q : Real) (Hp : real_lt real_zero p)
                  (Hq : real_lt real_zero q)
                  (eps : Real) (Heps : real_lt real_zero eps),
             real_le (real_mult (real_plus real_one real_one)
                                (real_plus p (real_opp q)))
                     (real_plus
                        (real_mult (real_plus real_one real_one)
                                   (real_kl_term p q Hp Hq))
                        (real_mult (real_plus real_one real_one)
                                   (real_mult p eps))))}}}}}}.
Proof.
  intros T T_pos energy.
  exact (existT _
           (fun s : unit => uap6t_bf_pos T T_pos energy s)
           (existT _
              (uap6t_Z_pos T T_pos energy)
              (existT _
                 (fun s : unit => uap6t_dist_pos T T_pos energy s)
                 (existT _
                    (uap6t_dist_normalized T T_pos energy)
                    (existT _
                       (uap6t_entropy_temp_explicit T T_pos energy)
                       (existT _
                          (fun (p q : Real) (Hp : real_lt real_zero p)
                                 (Hq : real_lt real_zero q) =>
                             uagfe_gibbs_temp_one_B p q Hp Hq)
                          (fun (p q : Real) (Hp : real_lt real_zero p)
                                 (Hq : real_lt real_zero q)
                                 (eps : Real) (Heps : real_lt real_zero eps) =>
                             uagfe_gibbs_temp_two_eps p q Hp Hq eps Heps))))))).
Qed.

(* ===================================================================== *)
(* b 面：EntropyMonoSplit 覆盖总装（A+B 两件对母件 11 枚）                  *)
(*   母件 11 枚编号（照母件头注序）：#1 emsi_bt / #2 emsi_bt_pos /          *)
(*   #3 emsi_kl（速记 Let 三枚——B 件以 uab_bt/uab_bt_pos/uab_kl 同形重建，  *)
(*   证书面经 #7–#11 出节形消费，此处以 C1 速记位正性件作覆盖证人）；       *)
(*   #4–#11 定理面八枚逐枚一行 Corollary。A 件出节形零换名（无节），        *)
(*   B 件出节形经 beta 转换对接（裸写 real_boltzmann_dist_temp /           *)
(*   real_KL_temp 洁净形，与 B 件 Let 换名形可转换）。                      *)
(* ===================================================================== *)

(* C1（覆盖 #1/#2 速记位）：重建 bt 位逐点正——上游直击（与 B 件            *)
(*   uab_bt_pos 同路：real_boltzmann_dist_temp_pos 一击）。                 *)
Corollary uapkg6_ems_cov_bt_pos :
  forall (S : Type) (rsu : (S -> Real) -> Real)
         (rsp : forall f : S -> Real,
                  (forall s : S, real_lt real_zero (f s)) ->
                  real_lt real_zero (rsu f))
         (u : Real) (Hu : real_lt real_zero u)
         (energy : S -> Real) (s : S),
    real_lt real_zero (real_boltzmann_dist_temp S rsu rsp u Hu energy s).
Proof.
  intros S rsu rsp u Hu energy s.
  exact (real_boltzmann_dist_temp_pos S rsu rsp u Hu energy s).
Qed.

(* C4（覆盖 #4 emsi_energy_pin_self）：A 件上游直击腿（uap63 零节直引）。 *)
Corollary uapkg6_ems_cov_pin_self :
  forall (S : Type) (rsu : (S -> Real) -> Real)
         (rsp : forall f : S -> Real,
                  (forall s : S, real_lt real_zero (f s)) ->
                  real_lt real_zero (rsu f))
         (energy : S -> Real) (u : Real) (Hu : real_lt real_zero u),
    real_eq
      (rsu (fun s : S =>
              real_mult
                (real_boltzmann_dist_temp S rsu rsp u Hu energy s)
                (energy s)))
      (real_energy_exp_temp S rsu rsp u Hu energy).
Proof.
  exact uap63_pin_self_updirect.
Qed.

(* C5（覆盖 #5 emsi_le_diff_ge_zero）：A 件独立链（eq 升 le 换向链）。    *)
Corollary uapkg6_ems_cov_diff_ge_zero :
  forall a b : Real,
    real_le a b -> real_le real_zero (real_plus b (real_opp a)).
Proof.
  exact uap63_diff_ge_zero_indep.
Qed.

(* C6（覆盖 #6 emsi_le_plus_eps）：A 件泛形直击腿。                       *)
Corollary uapkg6_ems_cov_plus_eps :
  forall X eps : Real,
    real_le real_zero X -> real_lt real_zero eps ->
    real_le real_zero (real_plus X eps).
Proof.
  exact uap63_plus_eps_updirect.
Qed.

(* C7（覆盖 #7 emsi_kl_ge_zero_eps_mirror）：B 件镜像换装（16 参全显，     *)
(*   温度位 T*；洁净形与 B 件出节形转换对接）。                            *)
Corollary uapkg6_ems_cov_kl_ge_zero_eps_mirror :
  forall (S : Type) (rsu : (S -> Real) -> Real)
         (rsp : forall f : S -> Real,
                  (forall s : S, real_lt real_zero (f s)) ->
                  real_lt real_zero (rsu f))
         (rse : forall f g : S -> Real,
                  (forall s : S, real_eq (f s) (g s)) ->
                  real_eq (rsu f) (rsu g))
         (rsl : forall f g : S -> Real,
                  (forall s : S, real_le (f s) (g s)) ->
                  real_le (rsu f) (rsu g))
         (rln : forall (a : Real) (f : S -> Real),
                  real_eq (rsu (fun s : S => real_mult a (f s)))
                          (real_mult a (rsu f)))
         (radd : forall f g : S -> Real,
                   real_eq (rsu (fun s : S => real_plus (f s) (g s)))
                           (real_plus (rsu f) (rsu g)))
         (T_star : Real) (HT : real_lt real_zero T_star)
         (energy p : S -> Real)
         (Hp : forall s : S, real_lt real_zero (p s))
         (Hnp : real_eq (rsu p) real_one)
         (eps : Real) (Heps : real_lt real_zero eps),
    real_le real_zero
      (real_plus (real_KL_temp S rsu rsp T_star HT energy p Hp) eps).
Proof.
  exact uab_kl_ge_zero_eps_mirror.
Qed.

(* C9（覆盖 #9 inst_pinned_at_peak）：B 件峰温点零前提封闭（洁净形）。    *)
Corollary uapkg6_ems_cov_pinned_at_peak :
  forall (S : Type) (rsu : (S -> Real) -> Real)
         (rsp : forall f : S -> Real,
                  (forall s : S, real_lt real_zero (f s)) ->
                  real_lt real_zero (rsu f))
         (T_star : Real) (HT : real_lt real_zero T_star)
         (energy : S -> Real),
    real_eq
      (rsu (fun s : S =>
              real_mult
                (real_boltzmann_dist_temp S rsu rsp T_star HT energy s)
                (energy s)))
      (real_energy_exp_temp S rsu rsp T_star HT energy).
Proof.
  exact uab_inst_pinned_at_peak.
Qed.

(* C8（覆盖 #8 inst_pinned）：B 件槽位1 Hpinned 装载（片运输供位显式）。  *)
Corollary uapkg6_ems_cov_inst_pinned :
  forall (S : Type) (rsu : (S -> Real) -> Real)
         (rsp : forall f : S -> Real,
                  (forall s : S, real_lt real_zero (f s)) ->
                  real_lt real_zero (rsu f))
         (T_star : Real) (HT : real_lt real_zero T_star)
         (energy : S -> Real),
    (forall (u : Real) (Hu : real_lt real_zero u),
       real_eq (real_energy_exp_temp S rsu rsp u Hu energy)
               (real_energy_exp_temp S rsu rsp T_star HT energy)) ->
    forall (u : Real) (Hu : real_lt real_zero u),
      real_eq
        (rsu (fun s : S =>
                real_mult
                  (real_boltzmann_dist_temp S rsu rsp u Hu energy s)
                  (energy s)))
        (real_energy_exp_temp S rsu rsp T_star HT energy).
Proof.
  exact uab_inst_pinned.
Qed.

(* C10（覆盖 #10 inst_kl_right）：B 件槽位2 Hkl_right 装载（KL_v 前位，   *)
(*   禁倒置红线照抄）。                                                    *)
Corollary uapkg6_ems_cov_inst_kl_right :
  forall (S : Type) (rsu : (S -> Real) -> Real)
         (rsp : forall f : S -> Real,
                  (forall s : S, real_lt real_zero (f s)) ->
                  real_lt real_zero (rsu f))
         (T_star : Real) (HT : real_lt real_zero T_star)
         (energy : S -> Real),
    (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
       real_le T_star u -> real_le u v ->
       real_le (real_KL_temp S rsu rsp T_star HT energy
                  (real_boltzmann_dist_temp S rsu rsp u Hu energy)
                  (real_boltzmann_dist_temp_pos S rsu rsp u Hu energy))
               (real_KL_temp S rsu rsp T_star HT energy
                  (real_boltzmann_dist_temp S rsu rsp v Hv energy)
                  (real_boltzmann_dist_temp_pos S rsu rsp v Hv energy))) ->
    forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
      real_le T_star u -> real_le u v ->
      forall eps : Real,
        real_lt real_zero eps ->
        real_le real_zero
          (real_plus
             (real_plus
                (real_KL_temp S rsu rsp T_star HT energy
                   (real_boltzmann_dist_temp S rsu rsp v Hv energy)
                   (real_boltzmann_dist_temp_pos S rsu rsp v Hv energy))
                (real_opp
                   (real_KL_temp S rsu rsp T_star HT energy
                      (real_boltzmann_dist_temp S rsu rsp u Hu energy)
                      (real_boltzmann_dist_temp_pos S rsu rsp u Hu energy))))
             eps).
Proof.
  exact uab_inst_kl_right.
Qed.

(* C11（覆盖 #11 inst_kl_left）：B 件槽位3 Hkl_left 装载（KL_u 前位镜像）。 *)
Corollary uapkg6_ems_cov_inst_kl_left :
  forall (S : Type) (rsu : (S -> Real) -> Real)
         (rsp : forall f : S -> Real,
                  (forall s : S, real_lt real_zero (f s)) ->
                  real_lt real_zero (rsu f))
         (T_star : Real) (HT : real_lt real_zero T_star)
         (energy : S -> Real),
    (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
       real_le u v -> real_le v T_star ->
       real_le (real_KL_temp S rsu rsp T_star HT energy
                  (real_boltzmann_dist_temp S rsu rsp v Hv energy)
                  (real_boltzmann_dist_temp_pos S rsu rsp v Hv energy))
               (real_KL_temp S rsu rsp T_star HT energy
                  (real_boltzmann_dist_temp S rsu rsp u Hu energy)
                  (real_boltzmann_dist_temp_pos S rsu rsp u Hu energy))) ->
    forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
      real_le u v -> real_le v T_star ->
      forall eps : Real,
        real_lt real_zero eps ->
        real_le real_zero
          (real_plus
             (real_plus
                (real_KL_temp S rsu rsp T_star HT energy
                   (real_boltzmann_dist_temp S rsu rsp u Hu energy)
                   (real_boltzmann_dist_temp_pos S rsu rsp u Hu energy))
                (real_opp
                   (real_KL_temp S rsu rsp T_star HT energy
                      (real_boltzmann_dist_temp S rsu rsp v Hv energy)
                      (real_boltzmann_dist_temp_pos S rsu rsp v Hv energy))))
             eps).
Proof.
  exact uab_inst_kl_left.
Qed.

(* b 面收口：打包 completeness 句（sigT 五层）——差分桥/eps 桥 A 独立链     *)
(*   与 B 重建链双链同语句并列（#5/#6 双覆盖）＋A 件 #5∘#6 组合桥。        *)
Corollary uapkg6_ems_coverage_complete :
  {_ : (forall a b : Real,
          real_le a b -> real_le real_zero (real_plus b (real_opp a))) &
   {_ : (forall X eps : Real,
           real_le real_zero X -> real_lt real_zero eps ->
           real_le real_zero (real_plus X eps)) &
   {_ : (forall a b eps : Real,
           real_le a b -> real_lt real_zero eps ->
           real_le real_zero (real_plus (real_plus b (real_opp a)) eps)) &
   {_ : (forall a b : Real,
           real_le a b -> real_le real_zero (real_plus b (real_opp a))) &
        (forall X eps : Real,
           real_le real_zero X -> real_lt real_zero eps ->
           real_le real_zero (real_plus X eps))}}}}.
Proof.
  exact (existT _
           uap63_diff_ge_zero_indep
           (existT _
              uap63_plus_eps_updirect
              (existT _
                 uap63_diff_eps_combo_indep
                 (existT _ uab_le_diff_ge_zero uab_le_plus_eps)))).
Qed.

(* ===================================================================== *)
(* c 面：喂件族整合（S5SlotWire＋ZPosLowRef＋ConcMixSelFeed）               *)
(*   抽象接口面：任意 RealInterfaceEnhanced 载体上三喂件代表位（协方差正、  *)
(*   产率恒等、逆元加法链）；Section 面照 S5SlotWire/ZPosLowRef 源 preamble *)
(*   镜像，出节 {RI}{DO} 换名 Lets 与两件源节同构。                         *)
(* ===================================================================== *)
Section Uapkg6FeedRI.

Context {RI : RealInterfaceEnhanced}.
Context {DO : DecidableOrder RI}.
Local Existing Instance RI_base.

Let R := @S01_BaseRing.R RI.
Let zero := @S01_BaseRing.zero RI.
Let one := @S01_BaseRing.one RI.
Let plus := @S01_BaseRing.plus RI.
Let mult := @S01_BaseRing.mult RI.
Let le := @S01_BaseRing.le RI.
Let lt := @S01_BaseRing.lt RI.
Let inv_pos := @S01_BaseRing.inv_pos RI.

Theorem uapkg6_feeder_ri_abstract :
  {_ : lt zero (fa56_covariance one one) &
   {_ : Id (fa56c_entropy_production_rate unit unit
              (fun _ : unit => one) (fun _ : unit => one) tt tt)
           (mult one one) &
        (forall (a b c d : R) (Ha : lt zero a) (Hb : lt zero b),
           lt a b -> le c d ->
           lt (plus (inv_pos b Hb) c) (plus (inv_pos a Ha) d))}}.
Proof.
  exact (existT _
           uassw_covariance_unit_pos
           (existT _
              uassw_entropy_production_unit
              (fun (a b c d : R) (Ha : lt zero a) (Hb : lt zero b)
                     (Hab : lt a b) (Hcd : le c d) =>
                 uazlr_lf4_plus_inv_chain a b c d Ha Hb Hab Hcd))).
Qed.

End Uapkg6FeedRI.

(* 具体实例面：Q 数值衰减喂件（S5SlotWire 槽9a）＋ConcMixSelFeed 两喂点     *)
(* ＋ZPosLowRef 配分正性喂点（RealEnhancedReal 具体实例，零接口槽）。       *)
Open Scope Q_scope.
Theorem uapkg6_feeder_concrete_faces :
  {_ : Qle (Qabs (gsq_grad (1#2)
                   (gsq_iter (1#2) (1#2) (O + Datatypes.S O) (1#2))))
           (gsq_pow (gsq_kappa (1#2) (1#2)) (Datatypes.S O)
              * Qabs (gsq_grad (1#2)
                        (gsq_iter (1#2) (1#2) O (1#2)))) &
   {_ : RealInterfaceEnhancedMod.le
          RealInterfaceEnhancedMod.zero RealInterfaceEnhancedMod.one &
   {_ : Id (csm_sumf bool uacms_en_bool
              (fun _ : bool => RealInterfaceEnhancedMod.one))
           (RealInterfaceEnhancedMod.plus RealInterfaceEnhancedMod.one
              (RealInterfaceEnhancedMod.plus RealInterfaceEnhancedMod.one
                 RealInterfaceEnhancedMod.zero)) &
        lt zero (@UpReqAttnGibbs.Z_thermo_r Real RealEnhancedReal unit
                   (@sumd_sumf Real RealEnhancedReal unit
                      (tt :: Datatypes.nil)%list)
                   real_one real_lt_zero_one
                   (fun _ : unit => real_one))}}}.
Proof.
  exact (existT _
           uassw_full_sign_decay_half
           (existT _
              uacms_zero_le_one
              (existT _ uacms_sumf_bool_eval uazlr_zsf_gibbs_thermo_r_unit))).
Qed.
Close Scope Q_scope.

(* ===================================================================== *)
(* d 面：战役总装 Corollary——论文6 五独占模块假设供给闭合一揽子            *)
(*   支1 GibbsFamilyExt：对称 Jeffreys 温度面（点态旗舰）。                 *)
(*   支2 TempDefs：温度节参全槽供给核心两枚（配分正＋归一化）。             *)
(*   支3 FepIdConsume 零槽：具体柯西实例识别面 Gibbs==Boltzmann（该支零     *)
(*      接口槽——识别类实例 FepIdentificationReal 构造性在场，无供位欠账）。 *)
(*   支4 EntropyMonoSplitInst：A+B 覆盖链组合旗舰（#5∘#6 独立复合）。       *)
(*   支5 喂件族：具体实例面代表位（序证书）。                               *)
(* ===================================================================== *)
Corollary uapkg6_campaign_supply_closed :
  {_ : (forall (p q b : Real) (Hp : real_lt real_zero p)
               (Hq : real_lt real_zero q) (Hb : real_lt real_zero b),
          real_le_b real_zero
            (real_mult b (real_plus (real_kl_term p q Hp Hq)
                                    (real_kl_term q p Hq Hp)))) &
   {_ : (forall (T : Real) (T_pos : real_lt real_zero T)
                (energy : unit -> Real),
            {_ : real_lt real_zero (uap6t_Z T T_pos energy) &
                 real_eq (uap6t_sum1 (uap6t_dist T T_pos energy)) real_one}) &
   {_ : (forall s : bool,
            @RealInterfaceEnhancedMod.req Real
              RealInterfaceEnhancedMod.RealEnhancedReal
              (@fic_softmax_temp Real RealInterfaceEnhancedMod.RealEnhancedReal
                 FepIdentificationReal s)
              (@fic_boltzmann_dist Real RealInterfaceEnhancedMod.RealEnhancedReal
                 FepIdentificationReal s)) &
   {_ : (forall a b eps : Real,
            real_le a b -> real_lt real_zero eps ->
            real_le real_zero (real_plus (real_plus b (real_opp a)) eps)) &
        RealInterfaceEnhancedMod.le
          RealInterfaceEnhancedMod.zero RealInterfaceEnhancedMod.one}}}}.
Proof.
  exact (existT _
           (fun (p q b : Real) (Hp : real_lt real_zero p)
                  (Hq : real_lt real_zero q) (Hb : real_lt real_zero b) =>
              uagfe_jeffreys_sym_temp_B p q b Hp Hq Hb)
           (existT _
              (fun (T : Real) (T_pos : real_lt real_zero T)
                   (energy : unit -> Real) =>
                 existT _ (uap6t_Z_pos T T_pos energy)
                          (uap6t_dist_normalized T T_pos energy))
              (existT _
                 (fun s : bool => fic2_real_instance_gibbs_consume s)
                 (existT _ uap63_diff_eps_combo_indep
                          uacms_zero_le_one)))).
Qed.

(* ---------- 自检段（G4 口径：逐件 Closed 实证，十四连） ---------- *)
Print Assumptions uapkg6_temp_param_full_supply.
Print Assumptions uapkg6_ems_cov_bt_pos.
Print Assumptions uapkg6_ems_cov_pin_self.
Print Assumptions uapkg6_ems_cov_diff_ge_zero.
Print Assumptions uapkg6_ems_cov_plus_eps.
Print Assumptions uapkg6_ems_cov_kl_ge_zero_eps_mirror.
Print Assumptions uapkg6_ems_cov_pinned_at_peak.
Print Assumptions uapkg6_ems_cov_inst_pinned.
Print Assumptions uapkg6_ems_cov_inst_kl_right.
Print Assumptions uapkg6_ems_cov_inst_kl_left.
Print Assumptions uapkg6_ems_coverage_complete.
Print Assumptions uapkg6_feeder_ri_abstract.
Print Assumptions uapkg6_feeder_concrete_faces.
Print Assumptions uapkg6_campaign_supply_closed.

(* ===================================================================== *)
(* v2 收官合龙段 —— T238 / PA6-36 席（20260920；v1 段 L1-471 零改动纯追加） *)
(*                                                                       *)
(* 使命：v1（T221b 七件合龙）建于 EMS_C/UniformLimit/two_state/fka 四新绿  *)
(*   件之前——本段补齐四面，收官合龙：                                     *)
(*   ① EMS_C（合龙验证 15 Qed）覆盖 completeness 引用面：uac_e11_full_    *)
(*      muster 出节形全实参总装引证（语句面=五分量洁净展开形，             *)
(*      c_bt/c_bt_pos/c_kl 内联还原上游注册面）。                          *)
(*   ② UniformLimit（严格档首刀 3 Qed）供给引用：pa6ul_gamma_pos_supply/   *)
(*      pa6ul_gap_le_supply/pa6ul_strict_first_cut 三位一揽子（真名        *)
(*      UpReqAttnUniformLimit 1777 版装载——其依赖件隔离根消歧见台账）。    *)
(*   ③ two_state（12 Qed）整节实例引用：uab23_ts_second_law_eps 全实参     *)
(*      引证＋零前提锚闭形双向打包（anchor_closed_lower/upper）。          *)
(*   ④ fka（转发收编 1 Qed）装载腿引证＋战役总装 v2：九支供给闭合一揽子    *)
(*      升级句（v1 五支→v2 九支，每支引对应件真证）。                      *)
(*                                                                       *)
(* 纪律：v1 段与四件本体零改（只 Require）；真名件（UpReqAttnUniformLimit） *)
(*   装载根=本席消歧根（真名 1777 版 md5 55a448，旧 614 版 3c62ac 隔离在   *)
(*   链外）；出节签名经 pa636_probe 探针打表（禁声明面猜）；Set 层合取     *)
(*   sigT 打包；新增 6 枚真 Qed（前缀 uapkg6v2_）非转发冒充（每枚自带语    *)
(*   句面与证明，全实参消费上游出节形）；尾嵌 Print Assumptions 六连自检。 *)
(* ===================================================================== *)

(* ---------- v2 依赖面追加（显式点名；⑨：Import 载荷不透传） ---------- *)
Require Import UpAblP6_EntropyMonoSplit_C.
Require Import UpAblP6_UniformLimit.
Require Import UpAblP6_SecondLaw_two_state.
Require Import fka_weak_triangle_ref.
Require Import AttnHardLimit218.
Require Import UpReqAttnUniformLimit.
Require Import SecondLawQuantified.

(* ===================================================================== *)
(* ① EMS_C 覆盖 completeness 引用面：uac_e11_full_muster 总装引证          *)
(*   EMS_C 出节形（Section UpAblP6EmsC 卸出）：S/求和/正性/峰温对/能量     *)
(*   五参后接三证书槽（片运输/增长/衰减），结论=五分量嵌套 sigT。本席语句  *)
(*   面取洁净展开形（c_bt/c_bt_pos/c_kl 内联还原 real_boltzmann_dist_temp/ *)
(*   _pos/real_KL_temp 注册面），证项=全实参直配。                        *)
(* ===================================================================== *)
Corollary uapkg6v2_emsc_muster_total :
  forall (S : Type) (rsu : (S -> Real) -> Real)
         (rsp : forall f : S -> Real,
                  (forall s : S, real_lt real_zero (f s)) ->
                  real_lt real_zero (rsu f))
         (T_star : Real) (HT : real_lt real_zero T_star)
         (energy : S -> Real),
    (forall (u : Real) (Hu : real_lt real_zero u),
       real_eq (real_energy_exp_temp S rsu rsp u Hu energy)
               (real_energy_exp_temp S rsu rsp T_star HT energy)) ->
    (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
       real_le T_star u -> real_le u v ->
       real_le (real_KL_temp S rsu rsp T_star HT energy
                  (real_boltzmann_dist_temp S rsu rsp u Hu energy)
                  (real_boltzmann_dist_temp_pos S rsu rsp u Hu energy))
               (real_KL_temp S rsu rsp T_star HT energy
                  (real_boltzmann_dist_temp S rsu rsp v Hv energy)
                  (real_boltzmann_dist_temp_pos S rsu rsp v Hv energy))) ->
    (forall (u v : Real) (Hu : real_lt real_zero u) (Hv : real_lt real_zero v),
       real_le u v -> real_le v T_star ->
       real_le (real_KL_temp S rsu rsp T_star HT energy
                  (real_boltzmann_dist_temp S rsu rsp v Hv energy)
                  (real_boltzmann_dist_temp_pos S rsu rsp v Hv energy))
               (real_KL_temp S rsu rsp T_star HT energy
                  (real_boltzmann_dist_temp S rsu rsp u Hu energy)
                  (real_boltzmann_dist_temp_pos S rsu rsp u Hu energy))) ->
    {_ : (forall (u : Real) (Hu : real_lt real_zero u),
            real_eq (rsu (fun s : S => real_mult
                              (real_boltzmann_dist_temp S rsu rsp u Hu energy s)
                              (energy s)))
                    (real_energy_exp_temp S rsu rsp T_star HT energy)) &
     {_ : (forall (u v : Real) (Hu : real_lt real_zero u)
                 (Hv : real_lt real_zero v),
             real_le T_star u -> real_le u v ->
             forall eps : Real, real_lt real_zero eps ->
             real_le real_zero
               (real_plus
                  (real_plus
                     (real_KL_temp S rsu rsp T_star HT energy
                        (real_boltzmann_dist_temp S rsu rsp v Hv energy)
                        (real_boltzmann_dist_temp_pos S rsu rsp v Hv energy))
                     (real_opp
                        (real_KL_temp S rsu rsp T_star HT energy
                           (real_boltzmann_dist_temp S rsu rsp u Hu energy)
                           (real_boltzmann_dist_temp_pos S rsu rsp u Hu energy))))
                  eps)) &
     {_ : (forall (u v : Real) (Hu : real_lt real_zero u)
                 (Hv : real_lt real_zero v),
             real_le u v -> real_le v T_star ->
             forall eps : Real, real_lt real_zero eps ->
             real_le real_zero
               (real_plus
                  (real_plus
                     (real_KL_temp S rsu rsp T_star HT energy
                        (real_boltzmann_dist_temp S rsu rsp u Hu energy)
                        (real_boltzmann_dist_temp_pos S rsu rsp u Hu energy))
                     (real_opp
                        (real_KL_temp S rsu rsp T_star HT energy
                           (real_boltzmann_dist_temp S rsu rsp v Hv energy)
                           (real_boltzmann_dist_temp_pos S rsu rsp v Hv energy))))
                  eps)) &
     {_ : real_eq (real_energy_exp_temp S rsu rsp T_star HT energy)
                  (rsu (fun s : S => real_mult
                              (real_boltzmann_dist_temp S rsu rsp T_star HT
                                 energy s)
                              (energy s))) &
          (forall a b : Real, real_le a b ->
             real_le real_zero
               (real_plus (real_plus b (real_opp a)) real_one))}}}}.
Proof.
  intros S rsu rsp T_star HT energy Hslice Hgrowth Hdecay.
  exact (uac_e11_full_muster S rsu rsp T_star HT energy Hslice Hgrowth Hdecay).
Qed.

(* ===================================================================== *)
(* ② UniformLimit 严格档供给引用：三件一揽子（γ>0 直配＋真间隙 gap_le＋    *)
(*   严格档主槽首刀放电）。语句面照上游槽形逐字（P7-50：真异点 x=false、   *)
(*   γ:=real_one 取等紧界、非空泛实例化——引用面全实参防转发冒充）。       *)
(* ===================================================================== *)
Corollary uapkg6v2_unilim_strict_supply :
  {_ : real_lt real_zero pa6ul_gamma &
   {_ : (forall x : bool, Not (Id x true) ->
           real_le (real_plus (pa6ul_z x) pa6ul_gamma) (pa6ul_z true)) &
        (forall eps : Real, real_lt real_zero eps ->
           sigT (fun T0 : Real =>
             And (real_lt real_zero T0)
               (forall (T : Real) (Ht : real_lt real_zero T),
                 real_lt T T0 ->
                 real_le
                   (real_list_sum bool
                      (fun x : bool =>
                         real_abs (real_minus_r
                             (alm_uniform bool pa6ul_vocab pa6ul_eq_dec true
                                pa6ul_m_in x)
                             (w_T bool pa6ul_vocab pa6ul_vocab_ne pa6ul_z T Ht
                                x)))
                      pa6ul_vocab)
                   eps)))}}.
Proof.
  exact (existT _
           pa6ul_gamma_pos_supply
           (existT _ pa6ul_gap_le_supply pa6ul_strict_first_cut)).
Qed.

(* ===================================================================== *)
(* ③ two_state 整节实例引用：SlqSecondLaw 列表和机器 two_state 实例面      *)
(*   （uab23_ts_second_law_eps 全实参引证）。                              *)
(* ===================================================================== *)
Corollary uapkg6v2_ts_second_law_face :
  forall (T : Real) (Ht : real_lt real_zero T) (energy p : ts_state -> Real)
         (Hp : forall s : ts_state, real_lt real_zero (p s))
         (Hnp : real_eq (ts_lsumf p) real_one)
         (Henergy : real_eq
                      (ts_lsumf (fun s : ts_state =>
                                   real_mult (p s) (energy s)))
                      (real_energy_exp_temp ts_state ts_lsumf ts_lsumpos T Ht
                         energy))
         (eps : Real) (Heps : real_lt real_zero eps),
    real_le (real_entropy_dist ts_state ts_lsumf p Hp)
            (real_plus
               (real_entropy_dist ts_state ts_lsumf
                  (slq_boltz ts_state ts_lsumf ts_lsumpos T Ht energy)
                  (slq_boltz_pos ts_state ts_lsumf ts_lsumpos T Ht energy))
               eps).
Proof.
  exact uab23_ts_second_law_eps.
Qed.

(* ③ 锚闭形：零前提实例钉（T:=real_one、p:=Boltzmann 自身）双向打包——     *)
(*   KL−增益 ≤ eps 与 增益−KL ≤ eps 两向同收（uab23_ts_anchor_closed_*）。 *)
Corollary uapkg6v2_ts_anchor_two_side :
  forall eps : Real, real_lt real_zero eps ->
    {_ : real_le
           (real_minus_r
              (slq_kl_cur_boltz ts_state ts_sumf uab23_ts_sumpos real_one
                 real_lt_zero_one ts_energy uab23_ts_boltz_one
                 uab23_ts_boltz_one_pos)
              (slq_entropy_gain ts_state ts_sumf uab23_ts_sumpos real_one
                 real_lt_zero_one ts_energy uab23_ts_boltz_one
                 uab23_ts_boltz_one_pos))
           eps &
     real_le
       (real_minus_r
          (slq_entropy_gain ts_state ts_sumf uab23_ts_sumpos real_one
             real_lt_zero_one ts_energy uab23_ts_boltz_one
             uab23_ts_boltz_one_pos)
          (slq_kl_cur_boltz ts_state ts_sumf uab23_ts_sumpos real_one
             real_lt_zero_one ts_energy uab23_ts_boltz_one
             uab23_ts_boltz_one_pos))
       eps}.
Proof.
  intros eps Heps.
  exact (existT _ (uab23_ts_anchor_closed_lower eps Heps)
                  (uab23_ts_anchor_closed_upper eps Heps)).
Qed.

(* ===================================================================== *)
(* ④ fka 转发收编引证＋战役总装 v2（本节上下文照 S01/fa53/WTC/fka 同款     *)
(*   Section 定式：Context {RI}{DO}＋RI_base 实例桥＋裸名 Let 桥）。       *)
(* ===================================================================== *)
Section Uapkg6V2Fka.

Context {RI : RealInterfaceEnhanced}.
Context {DO : DecidableOrder RI}.
Local Existing Instance RI_base.

Let R := @S01_BaseRing.R RI.
Let le := @S01_BaseRing.le RI.
Let mult := @S01_BaseRing.mult RI.
Let plus := @S01_BaseRing.plus RI.

(* ④ 引证位：二元 Gram 核装载腿（fka 转发收编件）洁净面直引——             *)
(*   语句面=fka 出节形同面，证项=@ 全显直给（T230 唯一校验点授权形）。     *)
Corollary uapkg6v2_fka_gram_face :
  forall a b c d : R,
    le (mult (plus (mult a c) (mult b d)) (plus (mult a c) (mult b d)))
       (mult (plus (mult a a) (mult b b)) (plus (mult c c) (mult d d))).
Proof.
  intros a b c d.
  exact (@fka_weak_triangle_ref RI DO a b c d).
Qed.

(* ===================================================================== *)
(* ④ 战役总装 v2：九支供给闭合一揽子升级句（v1 五支→v2 九支）——           *)
(*   支1 GibbsFamilyExt 对称 Jeffreys 温度面；支2 TempDefs 温度节参两枚；  *)
(*   支3 FepIdConsume 零槽 Gibbs==Boltzmann；支4 EMS A+B 覆盖链组合桥；    *)
(*   支5 喂件族具体实例面；支6 EMS_C 合龙验证零前提峰温对偶面；            *)
(*   支7 UniformLimit 严格档供给对（γ>0＋真间隙 gap_le）；                 *)
(*   支8 two_state 零前提锚闭双向；支9 fka 装载腿（本节载体面）。          *)
(*   九支证项齐指九件真证——任一支语句面错位即本件拒编。                    *)
(* ===================================================================== *)
Corollary uapkg6v2_campaign_supply_closed_v2 :
  {_ : (forall (p q b : Real) (Hp : real_lt real_zero p)
               (Hq : real_lt real_zero q) (Hb : real_lt real_zero b),
          real_le_b real_zero
            (real_mult b (real_plus (real_kl_term p q Hp Hq)
                                    (real_kl_term q p Hq Hp)))) &
   {_ : (forall (T : Real) (T_pos : real_lt real_zero T)
                (energy : unit -> Real),
            {_ : real_lt real_zero (uap6t_Z T T_pos energy) &
                 real_eq (uap6t_sum1 (uap6t_dist T T_pos energy)) real_one}) &
   {_ : (forall s : bool,
            @RealInterfaceEnhancedMod.req Real
              RealInterfaceEnhancedMod.RealEnhancedReal
              (@fic_softmax_temp Real RealInterfaceEnhancedMod.RealEnhancedReal
                 FepIdentificationReal s)
              (@fic_boltzmann_dist Real RealInterfaceEnhancedMod.RealEnhancedReal
                 FepIdentificationReal s)) &
   {_ : (forall a b eps : Real,
            real_le a b -> real_lt real_zero eps ->
            real_le real_zero (real_plus (real_plus b (real_opp a)) eps)) &
   {_ : RealInterfaceEnhancedMod.le
          RealInterfaceEnhancedMod.zero RealInterfaceEnhancedMod.one &
   {_ : (forall (Sc : Type) (rsu : (Sc -> Real) -> Real)
                (rsp : forall f : Sc -> Real,
                         (forall s : Sc, real_lt real_zero (f s)) ->
                         real_lt real_zero (rsu f))
                (Tc : Real) (HTc : real_lt real_zero Tc)
                (energy : Sc -> Real),
            real_eq (real_energy_exp_temp Sc rsu rsp Tc HTc energy)
                    (rsu (fun s : Sc => real_mult
                                (real_boltzmann_dist_temp Sc rsu rsp Tc HTc
                                   energy s)
                                (energy s)))) &
   {_ : real_lt real_zero pa6ul_gamma &
   {_ : (forall x : bool, Not (Id x true) ->
            real_le (real_plus (pa6ul_z x) pa6ul_gamma) (pa6ul_z true)) &
   {_ : (forall eps : Real, real_lt real_zero eps ->
            {_ : real_le
                   (real_minus_r
                      (slq_kl_cur_boltz ts_state ts_sumf uab23_ts_sumpos
                         real_one real_lt_zero_one ts_energy
                         uab23_ts_boltz_one uab23_ts_boltz_one_pos)
                      (slq_entropy_gain ts_state ts_sumf uab23_ts_sumpos
                         real_one real_lt_zero_one ts_energy
                         uab23_ts_boltz_one uab23_ts_boltz_one_pos))
                   eps &
                 real_le
                   (real_minus_r
                      (slq_entropy_gain ts_state ts_sumf uab23_ts_sumpos
                         real_one real_lt_zero_one ts_energy
                         uab23_ts_boltz_one uab23_ts_boltz_one_pos)
                      (slq_kl_cur_boltz ts_state ts_sumf uab23_ts_sumpos
                         real_one real_lt_zero_one ts_energy
                         uab23_ts_boltz_one uab23_ts_boltz_one_pos))
                   eps}) &
        (forall a b c d : R,
           le (mult (plus (mult a c) (mult b d))
                    (plus (mult a c) (mult b d)))
              (mult (plus (mult a a) (mult b b))
                    (plus (mult c c) (mult d d))))}}}}}}}}}.
Proof.
  exact (existT _
           (fun (p q b : Real) (Hp : real_lt real_zero p)
                   (Hq : real_lt real_zero q) (Hb : real_lt real_zero b) =>
              uagfe_jeffreys_sym_temp_B p q b Hp Hq Hb)
           (existT _
              (fun (T : Real) (T_pos : real_lt real_zero T)
                   (energy : unit -> Real) =>
                 existT _ (uap6t_Z_pos T T_pos energy)
                          (uap6t_dist_normalized T T_pos energy))
              (existT _
                 (fun s : bool => fic2_real_instance_gibbs_consume s)
                 (existT _ uap63_diff_eps_combo_indep
                 (existT _ uacms_zero_le_one
                 (existT _
                    (fun (Sc : Type) (rsu : (Sc -> Real) -> Real)
                           (rsp : forall f : Sc -> Real,
                                    (forall s : Sc, real_lt real_zero (f s)) ->
                                    real_lt real_zero (rsu f))
                           (Tc : Real) (HTc : real_lt real_zero Tc)
                           (energy : Sc -> Real) =>
                       uac_e9b_peak_sym Sc rsu rsp Tc HTc energy)
                    (existT _
                       pa6ul_gamma_pos_supply
                       (existT _
                          pa6ul_gap_le_supply
                          (existT _
                             (fun (eps : Real) (Heps : real_lt real_zero eps) =>
                                existT _ (uab23_ts_anchor_closed_lower eps Heps)
                                         (uab23_ts_anchor_closed_upper eps Heps))
                             (fun (a b c d : R) =>
                                fka_weak_triangle_ref RI DO a b c d)))))))))).
Qed.

End Uapkg6V2Fka.

(* ---------- v2 自检段（G4 口径：逐件 Closed 实证，六连） ---------- *)
Print Assumptions uapkg6v2_emsc_muster_total.
Print Assumptions uapkg6v2_unilim_strict_supply.
Print Assumptions uapkg6v2_ts_second_law_face.
Print Assumptions uapkg6v2_ts_anchor_two_side.
Print Assumptions uapkg6v2_fka_gram_face.
Print Assumptions uapkg6v2_campaign_supply_closed_v2.
