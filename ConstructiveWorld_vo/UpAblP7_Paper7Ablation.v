(* ============================================================ *)
(* UpAblP7_Paper7Ablation.v —— 论文7 专项消融战役 PA7-02 席首件            *)
(*   （Paper7Ablation 辖区·工法腿最小真件）                                *)
(* 母本：Paper7Ablation.v（席位P7A 六定理；本件只读消费，原树零改）          *)
(* 消费面（出口签名实测自探针件 Check 全显打表，2026-09-19）：              *)
(*   位1 p7a_delta_star_pos —— κ:=1−δ* 选择器供给（0 < δ* = lo²），        *)
(*       出口无可判定序扩展参数，N1 镜像 + N3 构造性二分之一实例；          *)
(*   位2 p7a_omd_pos —— 0 < 1−δ*（出口带可判定序参数面），N1 镜像；        *)
(*   位3 p7a_omd_lt_one —— 1−δ* < 1，N1 镜像 + N3 构造性二分之一实例；     *)
(*   位4 p7a_expf_wd —— 指数同余性消融（{正性,零点,加法} ⟹ 同余），        *)
(*       N1 接口镜像（论文7 §9.1 BoundedSoftmax 指数字段面冗余首刀）。      *)
(* 构造性实例（N3）：lo := inv_pos (plus one one) two_pos（二分之一抽象形），*)
(*   见证件 two_pos（S01:487 全局）+ inv_pos_pos（S01:237 类字段），        *)
(*   得 δ*=(1/2)²>0 与 1−δ*<1 的具体选择器供给（κ=3/4 落带内）；            *)
(*   避免 lo:=one 退化端点（彼处 1−δ*=0，正性件为假命题不供）。             *)
(* 分级：N1 镜像四件 + N3 实例两件（逐条真证，全 Qed）。                    *)
(* 依赖（只读消费，原树零改）：S01_BaseRing、Paper7Ablation。              *)
(* 姊妹席注记：Paper7Ablation 十四位 triage 归 PA7-01（T145 台账），本件    *)
(*   不做分级裁断，仅按上表消费面复验；两席写区互斥（T145/T146）。          *)
(* 红线自审：语句面全集合层；公理面零新增；独立伴生件不并入原模块；          *)
(*   前缀 uabp7_ 本件内防撞；全中文零承认件写法（头注与注释同口径）。        *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import Paper7Ablation.

(* ################ κ 选择器供给镜像（δ* 面 + 1−δ* 面） ################ *)
(* 节前导逐字复刻母件 P7aKappa/P7aExpf（隐参上下文 + 基类实例注册）。       *)
Section P7aMirrorKappa.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* 位1 ←p7a_delta_star_pos（N1 镜像；出口无序可判定参数面，隐参可统一） *)
Theorem uabp7_delta_star_pos_mirror :
  forall lo : R, lt zero lo -> lt zero (mult lo lo).
Proof.
  intros lo Hlo.
  exact (p7a_delta_star_pos lo Hlo).
Qed.

(* 位1' ←p7a_delta_star_pos @ lo := 二分之一（N3 构造性实例） *)
Theorem uabp7_delta_star_pos_half :
  lt zero (mult (inv_pos (plus one one) two_pos)
                (inv_pos (plus one one) two_pos)).
Proof.
  exact (p7a_delta_star_pos (inv_pos (plus one one) two_pos)
           (inv_pos_pos (plus one one) two_pos)).
Qed.

(* 位2 ←p7a_omd_pos（N1 镜像；母件证明不消费 lo_pos，出节无该前提位， *)
(*   语句逐字对齐出节形；出口带序可判定参数，全显喂本节位）            *)
Theorem uabp7_omd_pos_mirror :
  forall lo : R, lt (mult lo lo) one ->
    lt zero (minus one (mult lo lo)).
Proof.
  intros lo Hds.
  exact (@p7a_omd_pos RI DO lo Hds).
Qed.

(* 位3 ←p7a_omd_lt_one（N1 镜像） *)
Theorem uabp7_omd_lt_one_mirror :
  forall lo : R, lt zero lo -> lt (minus one (mult lo lo)) one.
Proof.
  intros lo Hlo.
  exact (@p7a_omd_lt_one RI DO lo Hlo).
Qed.

(* 位3' ←p7a_omd_lt_one @ 二分之一（N3 构造性实例；κ=3/4 上界面） *)
Theorem uabp7_omd_lt_one_half :
  lt (minus one (mult (inv_pos (plus one one) two_pos)
                      (inv_pos (plus one one) two_pos))) one.
Proof.
  exact (@p7a_omd_lt_one RI DO (inv_pos (plus one one) two_pos)
           (inv_pos_pos (plus one one) two_pos)).
Qed.

(* 位4 ←p7a_expf_wd（N1 接口镜像；同余性无须独立假设的实例化复验） *)
Theorem uabp7_expf_wd_mirror :
  forall (expf : R -> R)
         (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_plus : forall a b : R,
                        Id (expf (plus a b)) (mult (expf a) (expf b)))
         (a b : R), Id a b -> Id (expf a) (expf b).
Proof.
  intros expf expf_pos expf_zero expf_plus a b Hab.
  exact (p7a_expf_wd expf expf_pos expf_zero expf_plus a b Hab).
Qed.

End P7aMirrorKappa.

(* ============================================================ *)
(* 腿二（PA7-04 扩编）：§3 κ:=1−δ* 前件包合龙（论文 §6.3 引用面）           *)
(*   T145 建议：lo:=expf(invT·oppΔ) 别名 + AttnDoeblin:550 bs_lo_pos    *)
(*   直击 + :584 bs_delta_star_lt_one 喂母件 p7a_omd_pos 的 Hds 位。      *)
(*   装配：本节逐字复刻 AttnDoeblin BoundedSoftmax 的 invT/lo/hi/δ*      *)
(*   别名面（:547-:552）与上游四小件实例级链路（bs_lo_pos/bs_opp_lt/    *)
(*   bs_lo_lt_hi/bs_lo_hi_eq），得 δ*<1 实例真证（六件）；再 @ 全显喂    *)
(*   {RI}{DO} 对接母件 p7a_omd_pos/p7a_omd_lt_one（两件），以 S01:66    *)
(*   Set 层 And 收口为 κ∈(0,1) 前件包 Corollary（第九件，语句即          *)
(*   「0 < 1−δ* ∧ 1−δ* < 1」具体形，出节代入 lo 别名体）。              *)
(*   替代注记：lt_id_r_loc（S13:2230）与 S01:170 lt_id_r 同形同律，      *)
(*   一律用后者；包件三不走母件 opp_le_compat+opp 零恒等路线，改走      *)
(*   lt_zero_opp（S01:231）+ lt_le_iff（S01:160）+ le_lt_trans（S01:158） *)
(*   两步强链，两处皆免增 Require、原树零改。                           *)
(* ============================================================ *)
Section P7aKappaPackage.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

Variable temp : R.
Variable temp_pos : lt zero temp.
Variable Delta : R.
Variable Delta_pos : lt zero Delta.
Variable expf : R -> R.
Variable expf_pos : forall x : R, lt zero (expf x).
Variable expf_zero : Id (expf zero) one.
Variable expf_plus : forall a b : R, Id (expf (plus a b)) (mult (expf a) (expf b)).
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

(* 别名面：与 AttnDoeblin:547-:552 逐字同构（出节按母本式代入具体形） *)
Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).
Let delta_star := mult lo lo.

(* 包件一 ←bs_lo_pos（:550 直击，一跳 expf_pos） *)
Theorem uabp7_kappa_lo_pos : lt zero lo.
Proof.
  exact (expf_pos (mult invT (opp Delta))).
Qed.

(* 包件二 ←bs_hi_pos（:552 邻位；hi 侧正性备料） *)
Theorem uabp7_kappa_hi_pos : lt zero hi.
Proof.
  exact (expf_pos (mult invT Delta)).
Qed.

(* 包件三 ←bs_opp_lt（oppΔ < Δ；lt_zero_opp + lt_le_iff + le_lt_trans
   两步路线，不依赖 opp 零恒等） *)
Theorem uabp7_kappa_opp_lt : lt (opp Delta) Delta.
Proof.
  exact (le_lt_trans (opp Delta) zero Delta
           (lt_le_iff (opp Delta) zero (inl (lt_zero_opp Delta Delta_pos)))
           Delta_pos).
Qed.

(* 包件四 ←bs_lo_lt_hi（四步链：expf_mono_lt + lt_id_l + lt_id_r +
   lt_mult_compat；inv_pos_pos 供 invT 正性位） *)
Theorem uabp7_kappa_lo_lt_hi : lt lo hi.
Proof.
  apply (expf_mono_lt (mult invT (opp Delta)) (mult invT Delta)).
  apply (lt_id_l _ (mult (opp Delta) invT) _ (mult_comm invT (opp Delta))).
  apply (lt_id_r _ _ _ (mult_comm Delta invT)).
  exact (lt_mult_compat (opp Delta) Delta invT (inv_pos_pos temp temp_pos)
           uabp7_kappa_opp_lt).
Qed.

(* 包件五 ←bs_lo_hi_eq（expf 同态核心：lo·hi == one） *)
Theorem uabp7_kappa_lo_hi_eq : Id (mult lo hi) one.
Proof.
  apply (id_trans (id_sym (expf_plus (mult invT (opp Delta)) (mult invT Delta)))).
  apply (id_trans (id_cong expf (id_sym (distrib invT (opp Delta) Delta)))).
  apply (id_trans (id_cong expf (id_cong (fun w => mult invT w)
                 (id_trans (plus_comm (opp Delta) Delta) (plus_opp Delta))))).
  exact (id_trans (id_cong expf (mult_zero invT)) expf_zero).
Qed.

(* 包件六 ←bs_delta_star_lt_one（:584 实例级复刻：δ* := lo·lo < 1） *)
Theorem uabp7_kappa_ds_lt_one : lt delta_star one.
Proof.
  apply (lt_id_r _ _ _ uabp7_kappa_lo_hi_eq).
  apply (lt_id_r _ _ _ (mult_comm hi lo)).
  exact (lt_mult_compat lo hi lo uabp7_kappa_lo_pos uabp7_kappa_lo_lt_hi).
Qed.

(* 包件七 ←p7a_omd_pos @ 全显：:584 件喂 Hds 位（0 < 1−δ*） *)
Theorem uabp7_kappa_omd_pos_inst : lt zero (minus one delta_star).
Proof.
  exact (@p7a_omd_pos RI DO lo uabp7_kappa_ds_lt_one).
Qed.

(* 包件八 ←p7a_omd_lt_one @ 全显：:550 件喂 lo_pos 位（1−δ* < 1） *)
Theorem uabp7_kappa_omd_lt_one_inst : lt (minus one delta_star) one.
Proof.
  exact (@p7a_omd_lt_one RI DO lo uabp7_kappa_lo_pos).
Qed.

(* 包件九（合龙）：κ := 1−δ* ∈ (0,1) 前件包——论文 §6.3 引用形直呼面。
   语句即「0 < 1−δ* ∧ 1−δ* < 1」（S01:66 Set 层 And，零 Prop 泄露）。 *)
Corollary uabp7_kappa_in01_package :
  And (lt zero (minus one delta_star)) (lt (minus one delta_star) one).
Proof.
  exact (pair uabp7_kappa_omd_pos_inst uabp7_kappa_omd_lt_one_inst).
Qed.

End P7aKappaPackage.

(* ============================================================ *)
(* 腿三（PA7-04 扩编）：§2 有界 softmax 上界件的具体实例镜像                *)
(*   （P7aSoftBound 的 temp/Delta 双槽取 temp:=one、Delta:=one）。        *)
(*   T145 建议：one_pos（S01:218）+ inv_pos_pos（S01:237）+              *)
(*   lt_zero_opp（S01:231）链喂入。三件：位一=母件 §2 位3 的 one/one     *)
(*   实例镜像（探针实测出节序 Delta→Delta_pos→expf→expf_zero→           *)
(*   expf_mono_lt→invT→Hin，temp 槽未被母件本位消费故无该位）；          *)
(*   位二=字面 invT:=inv_pos one one_pos 处的链喂形；位三=独立四步链     *)
(*   复刻（零母件消费，逐字对齐母件 p7a_lo_lt_one 证明体）。             *)
(* ============================================================ *)
Section P7aSbInst.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Variable expf : R -> R.
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

(* 实例位一 ←p7a_lo_lt_one @ temp:=one、Delta:=one（N1 实例镜像） *)
Theorem uabp7_sb_one_lo_lt_one : forall invT : R,
  lt zero invT -> lt (expf (mult invT (opp one))) one.
Proof.
  intros invT Hin.
  exact (p7a_lo_lt_one one one_pos expf expf_zero expf_mono_lt invT Hin).
Qed.

(* 实例位二 ←p7a_lo_lt_one_instant @ one/one（N3 链喂：one_pos 双槽 +
   inv_pos_pos 造 invT:=inv_pos one one_pos） *)
Theorem uabp7_sb_one_lo_lt_one_instant :
  lt (expf (mult (inv_pos one one_pos) (opp one))) one.
Proof.
  exact (p7a_lo_lt_one_instant one one_pos one one_pos
           expf expf_zero expf_mono_lt).
Qed.

(* 实例位三（独立四步链复刻，零母件消费）：lt_zero_opp +
   lt_mult_compat + expf_mono_lt + expf_zero *)
Theorem uabp7_sb_one_lo_lt_one_chain :
  lt (expf (mult (inv_pos one one_pos) (opp one))) one.
Proof.
  assert (Hond := lt_zero_opp one one_pos).
  assert (Hm : lt (mult (opp one) (inv_pos one one_pos)) zero).
  { apply (lt_id_r (mult (opp one) (inv_pos one one_pos))
             (mult zero (inv_pos one one_pos)) zero
             (id_trans (mult_comm zero (inv_pos one one_pos))
                       (mult_zero (inv_pos one one_pos)))).
    exact (lt_mult_compat (opp one) zero (inv_pos one one_pos)
             (inv_pos_pos one one_pos) Hond). }
  apply (lt_id_r (expf (mult (inv_pos one one_pos) (opp one)))
           (expf zero) one expf_zero).
  apply (expf_mono_lt (mult (inv_pos one one_pos) (opp one)) zero).
  apply (lt_id_l (mult (inv_pos one one_pos) (opp one))
           (mult (opp one) (inv_pos one one_pos)) zero
           (mult_comm (inv_pos one one_pos) (opp one))).
  exact Hm.
Qed.

End P7aSbInst.

(* ---- PA 收尾段（逐件 Closed 判读；G4 审查留痕面） ---- *)
Print Assumptions uabp7_delta_star_pos_mirror.
Print Assumptions uabp7_delta_star_pos_half.
Print Assumptions uabp7_omd_pos_mirror.
Print Assumptions uabp7_omd_lt_one_mirror.
Print Assumptions uabp7_omd_lt_one_half.
Print Assumptions uabp7_expf_wd_mirror.
Print Assumptions uabp7_kappa_lo_pos.
Print Assumptions uabp7_kappa_hi_pos.
Print Assumptions uabp7_kappa_opp_lt.
Print Assumptions uabp7_kappa_lo_lt_hi.
Print Assumptions uabp7_kappa_lo_hi_eq.
Print Assumptions uabp7_kappa_ds_lt_one.
Print Assumptions uabp7_kappa_omd_pos_inst.
Print Assumptions uabp7_kappa_omd_lt_one_inst.
Print Assumptions uabp7_kappa_in01_package.
Print Assumptions uabp7_sb_one_lo_lt_one.
Print Assumptions uabp7_sb_one_lo_lt_one_instant.
Print Assumptions uabp7_sb_one_lo_lt_one_chain.
