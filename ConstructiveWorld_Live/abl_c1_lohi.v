(* ==========================================================================
   abl_c1_lohi.v —— UpAblP7_LoHiSqueeze 键控待解参数的外置见证族消解供给。
   ── 使命：宿主键控登记的 23 个待解参数逐参数消解。以 S01_BaseRing 类
   RealInterfaceEnhanced 自带的 Id 面字段 exp_neg 构造具名见证 expf :=
   c1_expf := fun x => exp_neg (opp x)：expf_zero 经 plus_inv_unique 链＋
   id_cong＋exp_neg_zero 闭合；expf_mono_lt 经 opp_lt_compat＋exp_neg_decr
   反变合成；expf_pos 经 exp_neg_pos；temp_pos／Delta_pos 以 temp:=Delta:=one
   应用形消解。见证族对任意 RI : RealInterfaceEnhanced 全称成立，宿主件零
   字节动零级联。T 支＝23 参数逐参数具名见证闭式；P′ 支＝宿主 10 条语句的
   _closed 应用形闭合定理（全参应用一击闭合）。
   ── 依赖：S01_BaseRing（exp_neg 族／opp_lt_compat／exp_neg_decr／one_pos／
   plus_inv_unique／Id／id_trans／id_cong／And）；UpAblP7_LoHiSqueeze（池内
   宿主副本，应用形闭合面 Require；缓存根同名 vo 经影根 _c1_dep 剔名排除）。
   ── 对标行：Id 面类字段库内捕手＝S01_BaseRing 的 exp_neg／exp_neg_zero；
   req 面先例对照＝UpAblD1_expf_pack 的 uabd1x_expf_zero（real_eq 面变体）。
   ── 构造性注记：全件 Qed 真构造，零承认式声明、零悬置前提、零经典逻辑、
   零节变量声明位；语句面全 Set 层（lt／le／Id／And:=A*B 皆 S01 Set 版）；
   23 参数见证与 10 件 _closed 逐件 Print Assumptions 判 Closed；件尾
   Separate Extraction 单命令 28 名，以 Obj.magic 零为判据。
   ── 编译配方：池 cwd＝沙箱/现役/abl_r85_supply_pool；source Live 库根
   toolchain/env.sh && unset COQLIB ROCQLIB && ulimit -s 65532 后 nice -19
   rocq c -native-compiler no -Q _c1_dep "" abl_c1_lohi.v（影根 _c1_dep＝
   缓存根 536 vo 剔宿主名成 535 只读符号链接）；绿判＝EXIT=0／日志零 Error／
   vo 头 8 字节 436f7121 00015ff4／vo 新于 v；第五证 rocq check。
   ========================================================================== *)

Require Import S01_BaseRing.
Require Import UpAblP7_LoHiSqueeze.

Existing Instance RI_base.

(* ============================================================ *)
(* 区一 见证族核心（键控钥匙本体）：e^x := exp_neg ∘ opp          *)
(*   ——RI 全称通用 Id 面 expf 见证，库内首个（req 面先例         *)
(*   uabd1x_expf 系不适用于 Id 参数）；四 Qed。                     *)
(* ============================================================ *)

Definition c1_expf (RI : RealInterfaceEnhanced) : R -> R :=
  fun x => exp_neg (opp x).

(* 负零归零：plus_inv_unique 三步链（S01:2570 件内先例同款，类字段纯构造） *)
Lemma c1_opp_zero : forall RI : RealInterfaceEnhanced, Id (opp zero) zero.
Proof.
  intros RI.
  apply (plus_inv_unique zero (opp zero) zero).
  - exact (plus_opp zero).
  - exact (plus_zero zero).
Qed.

(* W 本体见证：Id (c1_expf zero) one —— c1_opp_zero ＋ id_cong ＋
   exp_neg_zero（S01:167 Id 面类字段直捕）三步链 *)
Theorem c1_expf_zero : forall RI : RealInterfaceEnhanced,
  Id (c1_expf RI zero) one.
Proof.
  intros RI.
  apply (id_trans (id_cong exp_neg (c1_opp_zero RI))).
  exact exp_neg_zero.
Qed.

(* 联动见证甲：expf_pos —— λ 见证 exp_neg_pos (opp x) 全称直给 *)
Theorem c1_expf_pos : forall (RI : RealInterfaceEnhanced) (x : R),
  lt zero (c1_expf RI x).
Proof. intros RI x. exact (exp_neg_pos (opp x)). Qed.

(* 联动见证乙：expf_mono_lt —— opp_lt_compat 反变＋exp_neg_decr
   反变合成正变（两次反变＝增函数） *)
Theorem c1_expf_mono_lt : forall (RI : RealInterfaceEnhanced) (a b : R),
  lt a b -> lt (c1_expf RI a) (c1_expf RI b).
Proof.
  intros RI a b H.
  exact (exp_neg_decr (opp b) (opp a) (opp_lt_compat a b H)).
Qed.

(* ============================================================ *)
(* 区二 应用形数据（宿主出节 Let 内联形的具名复刻；零 Qed）         *)
(*   temp:=Delta:=one 应用形（one_pos 消解两正性位）；invT:=inv_pos *)
(*   one one_pos；lo/hi 与宿主五节 Let 形逐字同构。               *)
(* ============================================================ *)

Definition c1_invT (RI : RealInterfaceEnhanced) : R := inv_pos one one_pos.
Definition c1_lo (RI : RealInterfaceEnhanced) : R :=
  c1_expf RI (mult (c1_invT RI) (opp one)).
Definition c1_hi (RI : RealInterfaceEnhanced) : R :=
  c1_expf RI (mult (c1_invT RI) one).

(* ============================================================ *)
(* 区三 键控挂起 23 位逐参数供给锚（T 支·参数面见证闭式）             *)
(*   参数号＝C 底册 §一 #22 现档行号；五节参数面同构（宿主件自身     *)
(*   即五节重复结构，引用登记理逐节具名供逐位核对）。                 *)
(* ============================================================ *)

(* ---- §1 LhsPair 节（宿主 :20-:83）：5 参数 :26/:28/:30/:31/:32 ---- *)

(* 参数 1（:26 temp_pos）参数面 lt zero temp @ temp:=one 应用形 *)
Theorem c1_lhsp_temp_pos : forall RI : RealInterfaceEnhanced, lt zero one.
Proof. intros RI. exact one_pos. Qed.

(* 参数 2（:28 Delta_pos）参数面 lt zero Delta @ Delta:=one 应用形 *)
Theorem c1_lhsp_Delta_pos : forall RI : RealInterfaceEnhanced, lt zero one.
Proof. intros RI. exact one_pos. Qed.

(* 参数 3（:30 expf_pos）参数面 forall x, lt zero (expf x) @ expf:=c1_expf 应用形 *)
Theorem c1_lhsp_expf_pos : forall (RI : RealInterfaceEnhanced) (x : R),
  lt zero (c1_expf RI x).
Proof. intros RI x. exact (c1_expf_pos RI x). Qed.

(* 参数 4（:31 expf_zero·W 本体）参数面 Id (expf zero) one @ expf:=c1_expf 应用形 *)
Theorem c1_lhsp_expf_zero : forall RI : RealInterfaceEnhanced,
  Id (c1_expf RI zero) one.
Proof. intros RI. exact (c1_expf_zero RI). Qed.

(* 参数 5（:32 expf_mono_lt）参数面 forall a b, lt a b -> lt (expf a) (expf b) *)
Theorem c1_lhsp_expf_mono_lt : forall (RI : RealInterfaceEnhanced) (a b : R),
  lt a b -> lt (c1_expf RI a) (c1_expf RI b).
Proof. intros RI a b H. exact (c1_expf_mono_lt RI a b H). Qed.

(* ---- §2 LhsStar 节（宿主 :89-:130）：5 参数 :96/:98/:100/:101/:102 ---- *)

Theorem c1_lhss_temp_pos : forall RI : RealInterfaceEnhanced, lt zero one.
Proof. intros RI. exact one_pos. Qed.

Theorem c1_lhss_Delta_pos : forall RI : RealInterfaceEnhanced, lt zero one.
Proof. intros RI. exact one_pos. Qed.

Theorem c1_lhss_expf_pos : forall (RI : RealInterfaceEnhanced) (x : R),
  lt zero (c1_expf RI x).
Proof. intros RI x. exact (c1_expf_pos RI x). Qed.

Theorem c1_lhss_expf_zero : forall RI : RealInterfaceEnhanced,
  Id (c1_expf RI zero) one.
Proof. intros RI. exact (c1_expf_zero RI). Qed.

Theorem c1_lhss_expf_mono_lt : forall (RI : RealInterfaceEnhanced) (a b : R),
  lt a b -> lt (c1_expf RI a) (c1_expf RI b).
Proof. intros RI a b H. exact (c1_expf_mono_lt RI a b H). Qed.

(* ---- §3 UahlPair 节（宿主 :141-:194）：5 参数 :147/:149/:151/:152/:153 ---- *)

Theorem c1_uahp_temp_pos : forall RI : RealInterfaceEnhanced, lt zero one.
Proof. intros RI. exact one_pos. Qed.

Theorem c1_uahp_Delta_pos : forall RI : RealInterfaceEnhanced, lt zero one.
Proof. intros RI. exact one_pos. Qed.

Theorem c1_uahp_expf_pos : forall (RI : RealInterfaceEnhanced) (x : R),
  lt zero (c1_expf RI x).
Proof. intros RI x. exact (c1_expf_pos RI x). Qed.

Theorem c1_uahp_expf_zero : forall RI : RealInterfaceEnhanced,
  Id (c1_expf RI zero) one.
Proof. intros RI. exact (c1_expf_zero RI). Qed.

Theorem c1_uahp_expf_mono_lt : forall (RI : RealInterfaceEnhanced) (a b : R),
  lt a b -> lt (c1_expf RI a) (c1_expf RI b).
Proof. intros RI a b H. exact (c1_expf_mono_lt RI a b H). Qed.

(* ---- §4 UahlStar 节（宿主 :200-:238）：5 参数 :207/:209/:211/:212/:213 ---- *)

Theorem c1_uahs_temp_pos : forall RI : RealInterfaceEnhanced, lt zero one.
Proof. intros RI. exact one_pos. Qed.

Theorem c1_uahs_Delta_pos : forall RI : RealInterfaceEnhanced, lt zero one.
Proof. intros RI. exact one_pos. Qed.

Theorem c1_uahs_expf_pos : forall (RI : RealInterfaceEnhanced) (x : R),
  lt zero (c1_expf RI x).
Proof. intros RI x. exact (c1_expf_pos RI x). Qed.

Theorem c1_uahs_expf_zero : forall RI : RealInterfaceEnhanced,
  Id (c1_expf RI zero) one.
Proof. intros RI. exact (c1_expf_zero RI). Qed.

Theorem c1_uahs_expf_mono_lt : forall (RI : RealInterfaceEnhanced) (a b : R),
  lt a b -> lt (c1_expf RI a) (c1_expf RI b).
Proof. intros RI a b H. exact (c1_expf_mono_lt RI a b H). Qed.

(* ---- §5 UahlSbInst 节（宿主 :244-:286）：3 参数 :251/:252/:253 ---- *)

Theorem c1_uasi_expf_pos : forall (RI : RealInterfaceEnhanced) (x : R),
  lt zero (c1_expf RI x).
Proof. intros RI x. exact (c1_expf_pos RI x). Qed.

Theorem c1_uasi_expf_zero : forall RI : RealInterfaceEnhanced,
  Id (c1_expf RI zero) one.
Proof. intros RI. exact (c1_expf_zero RI). Qed.

Theorem c1_uasi_expf_mono_lt : forall (RI : RealInterfaceEnhanced) (a b : R),
  lt a b -> lt (c1_expf RI a) (c1_expf RI b).
Proof. intros RI a b H. exact (c1_expf_mono_lt RI a b H). Qed.

(* ============================================================ *)
(* 区四 键控翻色闭合：宿主 10 语句见证族全参应用形（P' 支）          *)
(*    C1 一期施工指令 Part C 同构——23 参数见证族闭合 ⟹ 宿主语句    *)
(*   应用形全部闭合，键控解锁端到端实证。DO 携带件 DecidableOrder 出节  *)
(*   显式保留（P' 支构造性保留口径）；UahlHalf 留岛节照令不提供。    *)
(* ============================================================ *)

(* ---- LhsPair 三件（DO 自由·T 支闭合） ---- *)

Theorem c1_lhs_lo_lt_one_hi_closed :
  forall RI : RealInterfaceEnhanced, And (lt (c1_lo RI) one) (lt one (c1_hi RI)).
Proof.
  intros RI.
  exact (@lhs_lo_lt_one_hi RI one one_pos one one_pos (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Qed.

Theorem c1_lhs_lo_lt_hi_closed :
  forall RI : RealInterfaceEnhanced, lt (c1_lo RI) (c1_hi RI).
Proof.
  intros RI.
  exact (@lhs_lo_lt_hi RI one one_pos one one_pos (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Qed.

Theorem c1_lhs_delta_star_bounded_closed :
  forall RI : RealInterfaceEnhanced,
    And (lt zero (mult (c1_lo RI) (c1_lo RI)))
        (lt (mult (c1_lo RI) (c1_lo RI)) one).
Proof.
  intros RI.
  exact (@lhs_delta_star_bounded RI one one_pos one one_pos (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Qed.

(* ---- LhsStar 一件（DO 携带·P' 支保留） ---- *)

Theorem c1_lhs_omd_bounded_closed :
  forall (RI : RealInterfaceEnhanced) (DO : DecidableOrder RI),
    And (lt zero (minus one (mult (c1_lo RI) (c1_lo RI))))
        (lt (minus one (mult (c1_lo RI) (c1_lo RI))) one).
Proof.
  intros RI DO.
  exact (@lhs_omd_bounded RI DO one one_pos one one_pos (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Qed.

(* ---- UahlPair 三件（DO 自由·T 支闭合） ---- *)

Theorem c1_uahp_lo_lt_one_hi_closed :
  forall RI : RealInterfaceEnhanced, And (lt (c1_lo RI) one) (lt one (c1_hi RI)).
Proof.
  intros RI.
  exact (@uahl_lo_lt_one_hi RI one one_pos one one_pos (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Qed.

Theorem c1_uahp_lo_lt_hi_closed :
  forall RI : RealInterfaceEnhanced, lt (c1_lo RI) (c1_hi RI).
Proof.
  intros RI.
  exact (@uahl_lo_lt_hi RI one one_pos one one_pos (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Qed.

Theorem c1_uahp_delta_star_bounded_closed :
  forall RI : RealInterfaceEnhanced,
    And (lt zero (mult (c1_lo RI) (c1_lo RI)))
        (lt (mult (c1_lo RI) (c1_lo RI)) one).
Proof.
  intros RI.
  exact (@uahl_delta_star_bounded RI one one_pos one one_pos (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Qed.

(* ---- UahlStar 一件（DO 携带·P' 支保留） ---- *)

Theorem c1_uahs_omd_bounded_closed :
  forall (RI : RealInterfaceEnhanced) (DO : DecidableOrder RI),
    And (lt zero (minus one (mult (c1_lo RI) (c1_lo RI))))
        (lt (minus one (mult (c1_lo RI) (c1_lo RI))) one).
Proof.
  intros RI DO.
  exact (@uahl_omd_bounded RI DO one one_pos one one_pos (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Qed.

(* ---- UahlSbInst 两件（一 P' 支保留＋一 T 支闭合——出节核验：
      uahl_omd_bounded_one 证体经 @p7a_omd_pos 携 DO、
      uahl_lo_lt_hi_one 证体零 DO 不出节，逐件按实签名应用形） ---- *)

Theorem c1_uasi_omd_bounded_one_closed :
  forall (RI : RealInterfaceEnhanced) (DO : DecidableOrder RI),
    And (lt zero (minus one (mult (c1_lo RI) (c1_lo RI))))
        (lt (minus one (mult (c1_lo RI) (c1_lo RI))) one).
Proof.
  intros RI DO.
  exact (@uahl_omd_bounded_one RI DO (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Qed.

Theorem c1_uasi_lo_lt_hi_one_closed :
  forall RI : RealInterfaceEnhanced, lt (c1_lo RI) (c1_hi RI).
Proof.
  intros RI.
  exact (@uahl_lo_lt_hi_one RI (c1_expf RI)
           (c1_expf_pos RI) (c1_expf_zero RI) (c1_expf_mono_lt RI)).
Qed.

(* ============================================================ *)
(* 区五 检验区一：逐件 Print Assumptions（37 件全 Closed 判据）   *)
(* ============================================================ *)
Print Assumptions c1_opp_zero.
Print Assumptions c1_expf_zero.
Print Assumptions c1_expf_pos.
Print Assumptions c1_expf_mono_lt.
Print Assumptions c1_lhsp_temp_pos.
Print Assumptions c1_lhsp_Delta_pos.
Print Assumptions c1_lhsp_expf_pos.
Print Assumptions c1_lhsp_expf_zero.
Print Assumptions c1_lhsp_expf_mono_lt.
Print Assumptions c1_lhss_temp_pos.
Print Assumptions c1_lhss_Delta_pos.
Print Assumptions c1_lhss_expf_pos.
Print Assumptions c1_lhss_expf_zero.
Print Assumptions c1_lhss_expf_mono_lt.
Print Assumptions c1_uahp_temp_pos.
Print Assumptions c1_uahp_Delta_pos.
Print Assumptions c1_uahp_expf_pos.
Print Assumptions c1_uahp_expf_zero.
Print Assumptions c1_uahp_expf_mono_lt.
Print Assumptions c1_uahs_temp_pos.
Print Assumptions c1_uahs_Delta_pos.
Print Assumptions c1_uahs_expf_pos.
Print Assumptions c1_uahs_expf_zero.
Print Assumptions c1_uahs_expf_mono_lt.
Print Assumptions c1_uasi_expf_pos.
Print Assumptions c1_uasi_expf_zero.
Print Assumptions c1_uasi_expf_mono_lt.
Print Assumptions c1_lhs_lo_lt_one_hi_closed.
Print Assumptions c1_lhs_lo_lt_hi_closed.
Print Assumptions c1_lhs_delta_star_bounded_closed.
Print Assumptions c1_lhs_omd_bounded_closed.
Print Assumptions c1_uahp_lo_lt_one_hi_closed.
Print Assumptions c1_uahp_lo_lt_hi_closed.
Print Assumptions c1_uahp_delta_star_bounded_closed.
Print Assumptions c1_uahs_omd_bounded_closed.
Print Assumptions c1_uasi_omd_bounded_one_closed.
Print Assumptions c1_uasi_lo_lt_hi_one_closed.

(* ============================================================ *)
(* 区六 检验区二：「提取可消解」关（  参数级铁律）——     *)
(*   见证族 5 名＋参数锚 23 名单命令 Separate Extraction 全过＝     *)
(*   23 参数逐参数实测；Obj.magic 归因双桶账见交付报告。              *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Separate Extraction c1_expf c1_opp_zero c1_expf_zero c1_expf_pos
  c1_expf_mono_lt c1_lhsp_temp_pos c1_lhsp_Delta_pos c1_lhsp_expf_pos
  c1_lhsp_expf_zero c1_lhsp_expf_mono_lt c1_lhss_temp_pos c1_lhss_Delta_pos
  c1_lhss_expf_pos c1_lhss_expf_zero c1_lhss_expf_mono_lt c1_uahp_temp_pos
  c1_uahp_Delta_pos c1_uahp_expf_pos c1_uahp_expf_zero c1_uahp_expf_mono_lt
  c1_uahs_temp_pos c1_uahs_Delta_pos c1_uahs_expf_pos c1_uahs_expf_zero
  c1_uahs_expf_mono_lt c1_uasi_expf_pos c1_uasi_expf_zero c1_uasi_expf_mono_lt.
