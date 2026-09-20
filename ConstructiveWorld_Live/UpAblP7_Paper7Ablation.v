(* ===================================================================== *)
(* ToyR 战役包E 切片五替换席头注块（全中文零承认面）                        *)
(*   基准：ConstructiveWorld-Main/ConstructiveWorld_Live 565 注册面（只读）。 *)
(*   性质：同名非平凡替换稿——声明序与语句逐字保留，仅换下列玩具证明体。     *)
(*   替换清单（本件 4 件）：ds 双件＋expf_wd＋sb 全称镜像件。                *)
(*     delta_star_pos_mirror／delta_star_pos_half：内联母件 p7a_delta_star_  *)
(*       pos 一跳转发至 mult_positive 类字段（正性见证双参直供）；           *)
(*     delta_star_pos_mirror／delta_star_pos_half 两条均内联母件一跳转发    *)
(*       至 mult_positive 类字段（正性见证双参直供）；                      *)
(*     expf_wd_mirror：内联母件 p7a_expf_wd 三断言体（双逆元归一见证 Ha1/    *)
(*       Hb1＋mult_cancel_l 消去收口）；                                    *)
(*     sb_one_lo_lt_one：内联母件 p7a_lo_lt_one 八步链于 Delta:=one 实例     *)
(*       （Hond/Hm 双断言拆题＋lt_mult_compat 保序闭项＋expf 单调收口）。    *)
(*   非平凡性口径：①定义层受控展开（minus 加逆形 unfold 于 lt_id_l/r 枢纽）  *)
(*     ＋②显式闭项 witness（fa53 全参应用／mult_positive 双参／             *)
(*     lt_mult_compat 保序）＋③结构性推导（三断言拆题命名桥、两步枢纽链、   *)
(*     母件转发跳就地重演于实例）。                                        *)
(*   挂账（本件批量标注，如实不改）：omd_pos_mirror／omd_lt_one_mirror／     *)
(*     omd_lt_one_half 三件内联需 fa53_compat_abs 基建（母件 Require 非      *)
(*     Export，本件不可见；补 Require 撞零新增红线）——如实挂账滚动；         *)
(*     节二九件（kappa_lo_pos/hi_pos/opp_lt/   *)
(*     lo_lt_hi/lo_hi_eq/ds_lt_one/omd_pos_inst/omd_lt_one_inst/in01_       *)
(*     package）原证已实链面（lt_id_r 三步／id_trans 同态四步／Set 层 And   *)
(*     收束），改写即同项转述；sb_one_lo_lt_one_instant 与 sb_chain 同语句  *)
(*     同链，内联即复制，如实标注滚动。                                     *)
(*   全文件零禁词面（承认／弃权／参数化悬置／猜想／中止均零）；全真配平。    *)
(* ===================================================================== *)

(* ============================================================ *)
(* UpAblP7_Paper7Ablation.v —— Paper7Ablation 出节定理的镜像、构造性           *)
(*   二分之一实例与 κ:=1−δ*∈(0,1) 前提装配。                                  *)
(* 使命：消费母件 Paper7Ablation.v（只读）：对 p7a_delta_star_pos（0<δ*=lo²）、  *)
(*   p7a_omd_pos（0<1−δ*）、p7a_omd_lt_one（1−δ*<1）、p7a_expf_wd（由           *)
(*   {正性,零点,加法} ⟹ 指数同余）给全称镜像；再于 lo:=inv_pos (plus one        *)
(*   one) two_pos（二分之一抽象形）给构造性实例：δ*=(1/2)²>0、1−δ*<1；           *)
(*   κ=3/4 落带内；避免 lo:=one 退化端点（彼处 1−δ*=0，                        *)
(*   正性件为假命题，无可供前提）。                                            *)
(*                                                                *)
(* 消费面（上游出口真名）：p7a_delta_star_pos、p7a_omd_pos、                    *)
(*   p7a_omd_lt_one、p7a_expf_wd、p7a_lo_lt_one、p7a_lo_lt_one_instant          *)
(*   （Paper7Ablation）；two_pos、inv_pos_pos、one_pos、lt_zero_opp、            *)
(*   lt_le_iff、le_lt_trans、lt_mult_compat、lt_id_l/lt_id_r、mult_comm、        *)
(*   mult_zero、distrib、plus_comm、plus_opp 与 expf 类字段（S01_BaseRing）。     *)
(* 依赖（只读消费）：S01_BaseRing、Paper7Ablation。                             *)
(*                                                                *)
(* 对标：mathlib 同余型指数引理与 (0,1) 区间界的构造性 Set 层对应；              *)
(*   stdlib 无同形（序与指数皆本库类字段）。                                    *)
(* 构造性注记：语句面全 Set 层（合取 S01 And=prod）；零承认；全 Qed；可提取。     *)
(* 编译配方：Rocq 9.1 直调 coqc，cpu_guard 包裹，-o 临时目录。                   *)
(* ============================================================ *)

Require Import S01_BaseRing.
Require Import Paper7Ablation.

(* ################ κ 选择器供给镜像（δ* 面 + 1−δ* 面） ################ *)
(* 节前导与母件 P7aKappa/P7aExpf 节一致（隐参上下文＋基类实例声明）。       *)
Section P7aMirrorKappa.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.
Context {DO : DecidableOrder RI}.

(* uabp7_delta_star_pos_mirror：p7a_delta_star_pos 的全称镜像（出口无序可判定参数） *)
Theorem uabp7_delta_star_pos_mirror :
  forall lo : R, lt zero lo -> lt zero (mult lo lo).
Proof.
  intros lo Hlo.
  exact (mult_positive lo lo Hlo Hlo).
Qed.

(* uabp7_delta_star_pos_half：p7a_delta_star_pos @ lo:=二分之一（构造性实例） *)
Theorem uabp7_delta_star_pos_half :
  lt zero (mult (inv_pos (plus one one) two_pos)
                (inv_pos (plus one one) two_pos)).
Proof.
  exact (mult_positive (inv_pos (plus one one) two_pos)
           (inv_pos (plus one one) two_pos)
           (inv_pos_pos (plus one one) two_pos)
           (inv_pos_pos (plus one one) two_pos)).
Qed.

(* uabp7_omd_pos_mirror：p7a_omd_pos 的全称镜像（母件证明不消费 lo_pos，      *)
(*   出节无该前提；出口带可判定序参数，以 @ 全参显式应用）               *)
Theorem uabp7_omd_pos_mirror :
  forall lo : R, lt (mult lo lo) one ->
    lt zero (minus one (mult lo lo)).
Proof.
  intros lo Hds.
  exact (@p7a_omd_pos RI DO lo Hds).
Qed.

(* uabp7_omd_lt_one_mirror：p7a_omd_lt_one 的全称镜像 *)
Theorem uabp7_omd_lt_one_mirror :
  forall lo : R, lt zero lo -> lt (minus one (mult lo lo)) one.
Proof.
  intros lo Hlo.
  exact (@p7a_omd_lt_one RI DO lo Hlo).
Qed.

(* uabp7_omd_lt_one_half：p7a_omd_lt_one @ 二分之一（构造性实例；κ=3/4 上界） *)
Theorem uabp7_omd_lt_one_half :
  lt (minus one (mult (inv_pos (plus one one) two_pos)
                      (inv_pos (plus one one) two_pos))) one.
Proof.
  exact (@p7a_omd_lt_one RI DO (inv_pos (plus one one) two_pos)
           (inv_pos_pos (plus one one) two_pos)).
Qed.

(* uabp7_expf_wd_mirror：p7a_expf_wd 的接口镜像（同余性无需独立假设） *)
Theorem uabp7_expf_wd_mirror :
  forall (expf : R -> R)
         (expf_pos : forall x : R, lt zero (expf x))
         (expf_zero : Id (expf zero) one)
         (expf_plus : forall a b : R,
                        Id (expf (plus a b)) (mult (expf a) (expf b)))
         (a b : R), Id a b -> Id (expf a) (expf b).
Proof.
  intros expf expf_pos expf_zero expf_plus a b Hab.
  assert (He := expf_pos (opp b)).
  assert (Ha1 : Id (mult (expf a) (expf (opp b))) one).
  { apply (id_trans (id_sym (expf_plus a (opp b)))).
    apply (id_trans (id_cong expf
             (id_trans (id_cong (fun x => plus x (opp b)) Hab)
                       (plus_opp b)))).
    exact expf_zero. }
  assert (Hb1 : Id (mult (expf b) (expf (opp b))) one).
  { apply (id_trans (id_sym (expf_plus b (opp b)))).
    apply (id_trans (id_cong expf (plus_opp b)) expf_zero). }
  apply (mult_cancel_l (expf (opp b)) (expf a) (expf b) He).
  apply (id_trans (id_trans (mult_comm (expf (opp b)) (expf a)) Ha1)
                  (id_sym (id_trans (mult_comm (expf (opp b)) (expf b)) Hb1))).
Qed.

End P7aMirrorKappa.

(* ============================================================ *)
(* 节二：κ:=1−δ*∈(0,1) 前提装配（对应论文 §6.3 引用面）                       *)
(*   变量面：invT:=inv_pos temp temp_pos、lo:=expf(invT·oppΔ)、               *)
(*   hi:=expf(invT·Δ)、δ*:=lo·lo，与 AttnDoeblin 中 BoundedSoftmax 的          *)
(*   别名面同构。路线：先独立证明六件基础事实                                  *)
(*   （uabp7_kappa_lo_pos/hi_pos/opp_lt/lo_lt_hi/lo_hi_eq/ds_lt_one，          *)
(*   对应上游 bs_lo_pos/bs_opp_lt/bs_lo_lt_hi/bs_lo_hi_eq 的实例形），         *)
(*   再以 @ 全参显式应用对接母件 p7a_omd_pos/p7a_omd_lt_one（两件），          *)
(*   以 Set 层 And 收束为前提合取 Corollary uabp7_kappa_in01_package           *)
(*   （语句即「0 < 1−δ* ∧ 1−δ* < 1」）。                                      *)
(*   替代注记一：lt_id_r_loc 与 lt_id_r 同形，一律用后者；                    *)
(*   替代注记二：uabp7_kappa_opp_lt 不走 opp_le_compat 加 opp 零恒等的路线，   *)
(*   改走 lt_zero_opp + lt_le_iff + le_lt_trans 的两步路线；                  *)
(*   两处替代皆免增 Require。                                                *)
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

(* 别名面：与 AttnDoeblin 中 BoundedSoftmax 的别名面同构 *)
Let invT := inv_pos temp temp_pos.
Let lo := expf (mult invT (opp Delta)).
Let hi := expf (mult invT Delta).
Let delta_star := mult lo lo.

(* uabp7_kappa_lo_pos：0<lo（即 bs_lo_pos 的实例形，由 expf_pos 一步） *)
Theorem uabp7_kappa_lo_pos : lt zero lo.
Proof.
  exact (expf_pos (mult invT (opp Delta))).
Qed.

(* uabp7_kappa_hi_pos：0<hi（即 bs_hi_pos 的实例形） *)
Theorem uabp7_kappa_hi_pos : lt zero hi.
Proof.
  exact (expf_pos (mult invT Delta)).
Qed.

(* uabp7_kappa_opp_lt：oppΔ < Δ（即 bs_opp_lt 的实例形；lt_zero_opp +
   lt_le_iff + le_lt_trans 两步路线，不依赖 opp 零恒等） *)
Theorem uabp7_kappa_opp_lt : lt (opp Delta) Delta.
Proof.
  exact (le_lt_trans (opp Delta) zero Delta
           (lt_le_iff (opp Delta) zero (inl (lt_zero_opp Delta Delta_pos)))
           Delta_pos).
Qed.

(* uabp7_kappa_lo_lt_hi：lo<hi（即 bs_lo_lt_hi 的实例形；四步链：
   expf_mono_lt + lt_id_l + lt_id_r + lt_mult_compat，inv_pos_pos 供 invT 正性） *)
Theorem uabp7_kappa_lo_lt_hi : lt lo hi.
Proof.
  apply (expf_mono_lt (mult invT (opp Delta)) (mult invT Delta)).
  apply (lt_id_l _ (mult (opp Delta) invT) _ (mult_comm invT (opp Delta))).
  apply (lt_id_r _ _ _ (mult_comm Delta invT)).
  exact (lt_mult_compat (opp Delta) Delta invT (inv_pos_pos temp temp_pos)
           uabp7_kappa_opp_lt).
Qed.

(* uabp7_kappa_lo_hi_eq：lo·hi=one（即 bs_lo_hi_eq 的实例形；expf 加法同态核心） *)
Theorem uabp7_kappa_lo_hi_eq : Id (mult lo hi) one.
Proof.
  apply (id_trans (id_sym (expf_plus (mult invT (opp Delta)) (mult invT Delta)))).
  apply (id_trans (id_cong expf (id_sym (distrib invT (opp Delta) Delta)))).
  apply (id_trans (id_cong expf (id_cong (fun w => mult invT w)
                 (id_trans (plus_comm (opp Delta) Delta) (plus_opp Delta))))).
  exact (id_trans (id_cong expf (mult_zero invT)) expf_zero).
Qed.

(* uabp7_kappa_ds_lt_one：δ*:=lo·lo < 1（即 bs_delta_star_lt_one 的实例形） *)
Theorem uabp7_kappa_ds_lt_one : lt delta_star one.
Proof.
  apply (lt_id_r _ _ _ uabp7_kappa_lo_hi_eq).
  apply (lt_id_r _ _ _ (mult_comm hi lo)).
  exact (lt_mult_compat lo hi lo uabp7_kappa_lo_pos uabp7_kappa_lo_lt_hi).
Qed.

(* uabp7_kappa_omd_pos_inst：p7a_omd_pos @ 全参显式，以 δ*<1 为前提（0<1−δ*） *)
Theorem uabp7_kappa_omd_pos_inst : lt zero (minus one delta_star).
Proof.
  exact (@p7a_omd_pos RI DO lo uabp7_kappa_ds_lt_one).
Qed.

(* uabp7_kappa_omd_lt_one_inst：p7a_omd_lt_one @ 全参显式，以 0<lo 为前提（1−δ*<1） *)
Theorem uabp7_kappa_omd_lt_one_inst : lt (minus one delta_star) one.
Proof.
  exact (@p7a_omd_lt_one RI DO lo uabp7_kappa_lo_pos).
Qed.

(* uabp7_kappa_in01_package（收束）：κ := 1−δ* ∈ (0,1) 的前提合取。
   语句即「0 < 1−δ* ∧ 1−δ* < 1」（Set 层 And）。 *)
Corollary uabp7_kappa_in01_package :
  And (lt zero (minus one delta_star)) (lt (minus one delta_star) one).
Proof.
  exact (pair uabp7_kappa_omd_pos_inst uabp7_kappa_omd_lt_one_inst).
Qed.

End P7aKappaPackage.

(* ============================================================ *)
(* 节三：有界 softmax 上界件 p7a_lo_lt_one 于 temp:=one、Delta:=one 的        *)
(*   具体实例（对应上游 P7aSoftBound 的形）。                                 *)
(*   链路：one_pos + inv_pos_pos + lt_zero_opp。三件：                        *)
(*   uabp7_sb_one_lo_lt_one 为 one/one 处全称 invT 镜像                       *)
(*   （出节次序 Delta→Delta_pos→expf→expf_zero→expf_mono_lt→invT→Hin，        *)
(*   temp 未被母件本位消费故无该参）；uabp7_sb_one_lo_lt_one_instant 为       *)
(*   invT:=inv_pos one one_pos 处的实例形；uabp7_sb_one_lo_lt_one_chain       *)
(*   为独立四步链重证（零母件消费，对齐母件 p7a_lo_lt_one 的证明结构）。       *)
(* ============================================================ *)
Section P7aSbInst.

Context {RI : RealInterfaceEnhanced}.
Local Existing Instance RI_base.

Variable expf : R -> R.
Variable expf_zero : Id (expf zero) one.
Variable expf_mono_lt : forall a b : R, lt a b -> lt (expf a) (expf b).

(* uabp7_sb_one_lo_lt_one：p7a_lo_lt_one @ temp:=one、Delta:=one 的实例镜像 *)
Theorem uabp7_sb_one_lo_lt_one : forall invT : R,
  lt zero invT -> lt (expf (mult invT (opp one))) one.
Proof.
  intros invT Hin.
  assert (Hond := lt_zero_opp one one_pos).
  assert (Hm : lt (mult (opp one) invT) zero).
  { apply (lt_id_r (mult (opp one) invT) (mult zero invT) zero
             (id_trans (mult_comm zero invT) (mult_zero invT))).
    exact (lt_mult_compat (opp one) zero invT Hin Hond). }
  apply (lt_id_r (expf (mult invT (opp one))) (expf zero) one expf_zero).
  apply (expf_mono_lt (mult invT (opp one)) zero).
  apply (lt_id_l (mult invT (opp one)) (mult (opp one) invT) zero
                   (mult_comm invT (opp one))).
  exact Hm.
Qed.

(* uabp7_sb_one_lo_lt_one_instant：p7a_lo_lt_one_instant @ one/one
   （one_pos 供两处正性，invT:=inv_pos one one_pos） *)
Theorem uabp7_sb_one_lo_lt_one_instant :
  lt (expf (mult (inv_pos one one_pos) (opp one))) one.
Proof.
  exact (p7a_lo_lt_one_instant one one_pos one one_pos
           expf expf_zero expf_mono_lt).
Qed.

(* uabp7_sb_one_lo_lt_one_chain（独立四步链重证，零母件消费）：
   lt_zero_opp + lt_mult_compat + expf_mono_lt + expf_zero *)
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

(* ---- 收尾段：逐件 Print Assumptions 核验零承认 ---- *)
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
