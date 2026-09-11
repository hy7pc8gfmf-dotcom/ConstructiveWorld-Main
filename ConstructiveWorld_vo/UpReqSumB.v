(* ============================================================ *)
(* UpReqSumB.v —— 逐点 ≤_B 求和提升席（T3：real_list_sum_le_b_compat） *)
(*   工单：B形扩展建造队列-20260910.md 目标 3（两段交付：段1 长度机器    *)
(*   + 逐点基件；段2 nonneg 收口器收尾 + 完整 compat 主件）。           *)
(*                                                                *)
(* 主结果（全部 Set 层、零 Prop 泄露、纯 term-mode 组装）：             *)
(*   段1 sumb_lenR：自持 Real 层列表长度机器（Fixpoint，nil→0、        *)
(*        cons→1+lenR rest）——免 nat 桥：CW219 nat 嵌入系 AlgHelpers   *)
(*        节放电件，跨接口不可复用（冻结判词在案），本席 Real 归纳      *)
(*        自持，零接口依赖。                                           *)
(*   段1 sumb_lenR_nonneg：0 ≤ lenR l（归纳 + 逐项非负加法兼容）。      *)
(*   段1 sumb_sum_const：Σ(常数 c) == lenR l·c（归纳；S 步 = 分布律     *)
(*        + 一元换形，与 lenR 定义步同构——求和面核心换形底座）。        *)
(*   段2 sumb_list_sum_le_b：主件——逐点 ≤_B ⟹ 求和 ≤_B（n 元 Bishop  *)
(*        求和面，Fubini 型逐点提升）。给 δ>0：逐点 ≤_B 展开取同一 δ    *)
(*        （免 1/n 拆分——Bishop 序全称面 n 份同 δ 即足，这是本件与      *)
(*        plain-eps 拆分链的本质区别）；逐点取 lt 支经 Or 编码单向桥    *)
(*        升 real_le，real_list_sum_le 保序提升；Σ(g+δ) 换形为          *)
(*        Σg + lenR·δ（add + sum_const 两步）；非负系数收口器           *)
(*        （C:=lenR l，非负证书即段1 件）单步收口。                     *)
(*                                                                *)
(* 消费面（全 Require 已认证 .vo，零改写上游）：                        *)
(*   CW219 real_list_sum 引擎三件（L41491/41498/41543/41634，节放电    *)
(*   签名 X 首参——Check 探针实测）；UpRealLeB2 real_le_closure_b_nonneg *)
(*   （L102 非负系数收口器）；RealSetoid 组合器面（lt_le_iff_req /      *)
(*   le_id_l / le_id_r / eq_plus_compat）。                            *)
(*                                                                *)
(* 红线：零公理零未闭合证明（G1 禁词全零）；Set 层语句（real_le_b      *)
(* 为 Set 值 forall 型，结论零 Prop 泄露）；纯 term-mode 显式组装      *)
(* （real_eq 非 Id，禁 rewrite，全链 real_eq_trans/compat）；全        *)
(* Qed. 闭合；新件 Print Assumptions Closed（文末）。                  *)
(* 编译配方：coqc 9.0（与树内 .vo magic 90001 同轨，E359 先例）         *)
(*   coqc -Q . "" -Q "..\001" "" UpReqSumB.v（cpu_guard 包装零裸调，    *)
(*   邻席编译期经负载闸自然排队，绑核 1）。                             *)
(* ============================================================ *)

From Stdlib Require Import QArith.Qring.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.

(* ============================================================ *)
(* 段1 · S.1 自持长度机器：lenR（Real 层，免 nat 桥接口）               *)
(* ============================================================ *)

Fixpoint sumb_lenR (X : Type) (l : list X) : Real :=
  match l with
  | nil => real_zero
  | cons _ rest => real_plus real_one (sumb_lenR X rest)
  end.

(* ============================================================ *)
(* 段1 · S.2 长度非负：0 ≤ lenR l                                     *)
(*   归纳：cons 步 0 ≤ 1+lenR rest 经 (0+0 与 0 换形) + 逐项非负兼容。  *)
(* ============================================================ *)

Lemma sumb_lenR_nonneg : forall (X : Type) (l : list X),
  real_le real_zero (sumb_lenR X l).
Proof.
  intros X l. induction l as [| w rest IH]; simpl.
  - apply real_le_refl.
  - apply (RealSetoid.real_le_id_l (real_plus real_zero real_zero) real_zero
                                   (real_plus real_one (sumb_lenR X rest))).
    + apply real_plus_zero.
    + apply (real_le_plus_compat real_zero real_one real_zero (sumb_lenR X rest)).
      * exact (RealSetoid.real_lt_le_iff_req real_zero real_one (inl real_lt_zero_one)).
      * exact IH.
Qed.

(* ============================================================ *)
(* 段1 · S.3 常数和坍缩：Σ(常数 c) == lenR l·c                          *)
(*   归纳：cons 步 c + Σconst rest == c + lenR rest·c（IH）             *)
(*        == 1·c + lenR rest·c（一元换形）== (1+lenR rest)·c（分布律）。 *)
(* ============================================================ *)

Lemma sumb_sum_const : forall (X : Type) (c : Real) (l : list X),
  real_eq (real_list_sum X (fun _ : X => c) l) (real_mult (sumb_lenR X l) c).
Proof.
  intros X c l. induction l as [| w rest IH]; simpl.
  - (* 0 == 0·c：经 c·0 中项（mult_zero 零在右侧，comm 桥接） *)
    apply (real_eq_trans _ (real_mult c real_zero) _).
    + apply real_eq_sym. apply real_mult_zero.
    + apply real_mult_comm.
  - apply (real_eq_trans _
             (real_plus c (real_mult (sumb_lenR X rest) c)) _).
    + apply (RealSetoid.real_eq_plus_compat c
               (real_list_sum X (fun _ : X => c) rest)
               c
               (real_mult (sumb_lenR X rest) c)).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_eq_trans _
               (real_plus (real_mult real_one c)
                          (real_mult (sumb_lenR X rest) c)) _).
      * apply (RealSetoid.real_eq_plus_compat c
                 (real_mult (sumb_lenR X rest) c)
                 (real_mult real_one c)
                 (real_mult (sumb_lenR X rest) c)).
        -- (* c == 1·c：c·1 == c（mult_one 零在右侧）+ comm 桥 *)
           apply (real_eq_trans _ (real_mult c real_one) _).
           ++ apply real_eq_sym. apply real_mult_one.
           ++ apply real_mult_comm.
        -- apply real_eq_refl.
      * (* (1·c)+(lenR·c) == (1+lenR)·c：distrib_r 直连（方向同向，零翻转） *)
        apply real_distrib_r.
Qed.

(* ============================================================ *)
(* 段2 · S.4 主件：逐点 ≤_B 求和提升（n 元 Bishop 求和面）               *)
(*   sumb_list_sum_le_b：逐点 ≤_B ⟹ 求和 ≤_B。                          *)
(*   证明链（任务书规格单闭合设计）：                                    *)
(*     给 δ>0：逐点 ≤_B 展开取同一 δ（免 1/n 拆分——real_le_b 全称面     *)
(*     n 份同 δ 即足）；逐点取 lt 支经 Or 编码单向桥升 real_le           *)
(*     （判词 2 边界内：Or 编码仅作单向桥消费）；real_list_sum_le 保序   *)
(*     提升：Σf ≤ Σ(g+δ)；Σ(g+δ) == Σg + Σ(常数 δ) == Σg + lenR·δ       *)
(*     （add + 段1 sum_const 两步换形）；非负系数收口器单步收口          *)
(*     （C := lenR l，非负证书 = 段1 lenR_nonneg）。                     *)
(* ============================================================ *)

Lemma sumb_list_sum_le_b : forall (X : Type) (f g : X -> Real) (l : list X),
  (forall w : X, real_le_b (f w) (g w)) ->
  real_le_b (real_list_sum X f l) (real_list_sum X g l).
Proof.
  intros X f g l H.
  (* 零 unfold：收口器结论即 real_le_b 形直配（外层 δ 全称面由器消费，
     逐点统一 eps 发生在器前提的全称位内） *)
  apply (real_le_closure_b_nonneg
           (real_list_sum X f l)
           (real_list_sum X g l)
           (sumb_lenR X l)).
  - (* 前提 1：0 ≤ C := lenR l（段1 件） *)
    apply sumb_lenR_nonneg.
  - (* 前提 2：∀eps>0, Σf ≤ Σg + lenR·eps *)
    intros eps Heps.
    (* 逐点统一 eps：f w < g w + eps（lt 支）升 real_le（Or 编码 inl 单向桥） *)
    assert (Hpt : forall w : X, real_le (f w) (real_plus (g w) eps)).
    { intro w.
      exact (RealSetoid.real_lt_le_iff_req (f w) (real_plus (g w) eps)
               (inl (H w eps Heps))). }
    pose proof (real_list_sum_le X f (fun w : X => real_plus (g w) eps) l Hpt) as Hsum.
    (* 换形右端：Σ(g+eps) == Σg + Σ(常数 eps) == Σg + lenR·eps *)
    apply (RealSetoid.real_le_id_r
             (real_list_sum X f l)
             (real_list_sum X (fun w : X => real_plus (g w) eps) l)
             (real_plus (real_list_sum X g l)
                        (real_mult (sumb_lenR X l) eps))).
    + apply (real_eq_trans _
               (real_plus (real_list_sum X g l)
                          (real_list_sum X (fun _ : X => eps) l)) _).
      * apply (real_list_sum_add X g (fun _ : X => eps) l).
      * apply (RealSetoid.real_eq_plus_compat (real_list_sum X g l)
                 (real_list_sum X (fun _ : X => eps) l)
                 (real_list_sum X g l)
                 (real_mult (sumb_lenR X l) eps)).
        -- apply real_eq_refl.
        -- apply sumb_sum_const.
    + exact Hsum.
Qed.

(* ============================================================ *)
(* 尾注：诚实台账（本席增量判词，接 UpRealLeB2 判词 G1-G6）              *)
(*                                                                *)
(* 【判词 S1｜逐点统一 eps】sumb_list_sum_le_b：可证，且免 1/n 拆分。     *)
(*   根因：real_le_b 系 Set 值全称面（∀eps>0），n 元求和收口对每个        *)
(*   逐点件取同一 δ 即足——n 份 δ 并入右端后坍缩为 Σ(常数 δ)，由          *)
(*   sum_const 换形为 lenR·δ 一次性计账。这与 plain-eps 族的             *)
(*   eps/2 拆分链（leb2_half_add 底座）本质不同：全称余量在 Bishop       *)
(*   面天然可复制，无需构造性对半。                                      *)
(* 【判词 S2｜自持长度机器】sumb_lenR：Real 层 Fixpoint 三行自持，        *)
(*   零 nat 桥接口消费——CW219 nat 嵌入系节放电件跨接口不可复用          *)
(*   （冻结判词在案），本席绕开不消费。lenR 与 length 的数值对齐        *)
(*   无消费面（本设计零 nat 数值，全走 Real 归纳）。                      *)
(* 【判词 S3｜收口器选型】主件走非负系数器（C:=lenR l，证书              *)
(*   sumb_lenR_nonneg）——lenR 的正性（严格）对空表不成立（lenR nil      *)
(*   == 0），故 C>0 证书路线不可用，正是 real_le_closure_b_nonneg        *)
(*   （UpRealLeB2 L102）的规格场景；空表支路经收口器 C+1>0 的            *)
(*   证书加工面自然闭合，零分情形。                                      *)
(* 【判词 S4｜Or 编码消费边界】逐点升格仅消费单向桥（lt 支 inl →        *)
(*   real_le），与判词 2（Or 形 min 反例不可证）边界一致——本件           *)
(*   不主张 Or 形逐点前提升格。                                          *)
(* 【对账】任务书目标 3 规格四件（lenR/lenR_nonneg/sum_const/主件）      *)
(*   全部落盘本文件；前缀 sumb_ 全库零占用（leb3_ 系 T1 领地已用，        *)
(*   本席分区避让）。E360 判词 G2「组合器止步二元」自此补齐 n 元面。      *)
(* 【机器状态】四关卡：G1 禁词全零（含头注注记位）；G2 重编 EXIT=0；      *)
(*   G3 提取探针 Obj.magic 计数为零（探针验后删）；G4 coqchk 认证         *)
(*   9.0 同平台长窗通过。全件 Print Assumptions Closed（见文末）。        *)
(* ============================================================ *)

Print Assumptions sumb_lenR_nonneg.
Print Assumptions sumb_sum_const.
Print Assumptions sumb_list_sum_le_b.
