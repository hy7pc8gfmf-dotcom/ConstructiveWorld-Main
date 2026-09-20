(* ===================================================================== *)
(* ToyR 切片二横幅（T248 台账席续作，20260921）——本件为 ConcMixSelFeed 的    *)
(* ToyR 玩具证明体替换稿：消融50 同名件与基准树逐字同，按落件查重规走        *)
(* ToyR_ 前缀；定理名/语句面/Require 面/自检段与原件逐字一致，仅换九处      *)
(* 玩具单点转发证明体为实质重演体，尾 Print Assumptions 面原样保留。        *)
(* 九刀换轨路线（程序直取下层引擎，不消费各槽原金标准转发件）：              *)
(*   ①cms_lt_plus_compat_lt_le_sel ②cms_lt_plus_compat_lt_le_time          *)
(*     ⑩cms_bs_lpc（同体三槽）：real_le Or 拆支两路——lt 支直取双严格加法    *)
(*     引擎 real_lt_plus_compat；eq 支七步链（eq_plus_compat 键填充→        *)
(*     eq_lt_lt 桥→plus_comm 换位→lt_plus_translate 平移→comm 收口）        *)
(*   ③cms_sum_ext ④cms_sum_linear ⑤cms_sum_add ⑥cms_sum_le                 *)
(*     ⑧cms_sum_eq_list：csm_sumf 定义性展开（=sumd_list_sum 处方）后列表   *)
(*     归纳结构性重演——nil 支 zero 收口，cons 支 plus_compat 缝合腿；        *)
(*     linear 刀经 distrib 右分配引擎三段中项链；add 刀经交换律中项缝       *)
(*     合（req_plus_exchange）+归纳腿翻面；le 刀 le_plus_compat 直缝。       *)
(*   ⑨cms_bs_abs：real_le Or 拆支——lt 支 abs_pos 件；eq 支三段 eq_trans     *)
(*     链（abs_eq_compat 键填充→abs_zero 收口→原 eq 收口）。                 *)
(* 挂账（如实登记不硬凑）：⑦cms_bs_swap 双折和换序需外层归纳内外双重        *)
(*     重排（多中项交换/结合链复合），本切片未落刀，原转发体原样保留。       *)
(* 纪律：零新增 Require；Proof./Qed. 与原件 11/11 守恒；全中文零承认。      *)
(* ===================================================================== *)

(* ===================================================================== *)
(* ConcMixSelFeed.v — E-STAGING-CZX13 席位 / T84 缺口段候补4 施工件          *)
(* cms_ 前缀（全库 grep 零撞名，20260918 实测）。                          *)
(* 使命：UpReqConcMixSel 的 A 类槽放电总件——lt_plus×2 + sum 四槽 +         *)
(*       bs_swap + sum_eq_list（另收邻接伴件 bs_abs/bs_lpc，使 CmkMixTime  *)
(*       诚实接口 A 面 10 槽全清）。纯放电零新数学（T62 P1 同型），          *)
(*       对照 LowRefFeed4（lf4_）逐槽写消解宣言，四要素 =                  *)
(*       槽位坐标 / 原语句 / 接线引用 / 核销判词。                         *)
(*                                                                       *)
(* 【B 类护墙登记（T84 §2 定谳，本件零触碰）】                             *)
(*   ① abs_sum_le_h（CmkMixTime:754-755，plain 形冻结槽）：|Σf| ≤ Σ|f| 的   *)
(*      无条件 plain le 形——ConcSoftmax 头注定谳：real_le=Or(lt)(eq) 混合号 *)
(*      双支不可达，唯 Bishop 逐 eps 形 csm_abs_sum_le_eps 可供（或 B1 一元 *)
(*      档 cb1_abs_sum_le 平推）=B 永久槽，本件不喂不翻案。                 *)
(*   ② 数据位 10 枚（T84：enum/temp/Delta/z 等=实例供给数据位 B）：         *)
(*      S:739、sumf:740、enum:758、enum_nonempty:759、temp:760、temp_pos:  *)
(*      761、Delta:762、Delta_pos:763、z:764、z_lb:765、z_ub:766——实例     *)
(*      供给位，本件不喂。                                                 *)
(*   （故本件放电 = A 类 8 槽 + 邻接伴件 2 槽；abs_sum_le_h 留墙如定谳。）  *)
(*                                                                       *)
(* 【槽①】UpReqConcMixSel.v:79-80（Section CmkMixSelect）lt_plus_compat_  *)
(*   lt_le                                                                *)
(*   原语句：forall a b c d : R, lt a b -> le c d -> lt (plus a c)         *)
(*           (plus b d)（宿主 Context {R}{RIS} 抽象世界）                  *)
(*   接线引用：S07_RealSetoidExpLog.v:6118 real_lt_plus_compat_lt_le      *)
(*   （CW219 Real 层成品；UpReqConcB1 头注「AT6 报告 §五备选路线定谳：      *)
(*   抽象层不可内证、具体层已成品零重证」；cb1_mixing_cert 实喂先例）       *)
(*   判词：具体层（R := Real、RIS := RealEnhancedReal）一击收编，           *)
(*   出转发定理 cms_lt_plus_compat_lt_le_sel。                             *)
(*                                                                       *)
(* 【槽②】UpReqConcMixSel.v:736-737（Section CmkMixTime）同位镜像          *)
(*   原语句/接线引用同槽①（双节同位×2，T84「lt_plus_compat_lt_le×2」）     *)
(*   判词：同件同喂，出转发定理 cms_lt_plus_compat_lt_le_time。             *)
(*                                                                       *)
(* 【槽③】UpReqConcMixSel.v:743-744 sum_ext                               *)
(*   原语句：forall f g : S -> R, (forall s, req (f s) (g s)) ->           *)
(*           req (sumf f) (sumf g)（sumf 抽象 Variable:740）               *)
(*   接线引用：UpReqConcSoftmax.v:62 csm_sum_ext（sumd_sum_ext 委派，      *)
(*   T84「csm_ 五件委派先例」；折叠键 sumf := csm_sumf S en）              *)
(*   判词：键填充收编，出转发定理 cms_sum_ext。                            *)
(*                                                                       *)
(* 【槽④】UpReqConcMixSel.v:745-747 sum_linear                            *)
(*   原语句：forall a f, req (sumf (fun s => mult a (f s)))                *)
(*           (mult a (sumf f))                                            *)
(*   接线引用：UpReqConcSoftmax.v:67 csm_sum_linear（sumd_sum_linear 委派）*)
(*   判词：键填充收编，出转发定理 cms_sum_linear。                          *)
(*                                                                       *)
(* 【槽⑤】UpReqConcMixSel.v:748-750 sum_add                               *)
(*   原语句：forall f g, req (sumf (fun s => plus (f s) (g s)))            *)
(*           (plus (sumf f) (sumf g))                                     *)
(*   接线引用：UpReqConcSoftmax.v:72 csm_sum_add（sumd_sum_add 委派）       *)
(*   判词：键填充收编，出转发定理 cms_sum_add。                            *)
(*                                                                       *)
(* 【槽⑥】UpReqConcMixSel.v:751-752 sum_le                                *)
(*   原语句：forall f g, (forall s, le (f s) (g s)) -> le (sumf f)         *)
(*           (sumf g)                                                     *)
(*   接线引用：UpReqConcSoftmax.v:77 csm_sum_le（sumd_sum_le 委派）         *)
(*   判词：键填充收编，出转发定理 cms_sum_le。                             *)
(*                                                                       *)
(* 【槽⑦】UpReqConcMixSel.v:767-769 bs_swap                               *)
(*   原语句：forall f : S -> S -> R, req (sumf (fun s => sumf              *)
(*           (fun s' => f s s'))) (sumf (fun s' => sumf (fun s =>         *)
(*           f s s')))                                                    *)
(*   接线引用：UpReqConcB1.v:96 cb1_swap_lists（双折归纳泛型件，S/f/a/b    *)
(*   全参；cb1_mixing_cert 实喂先例 (fun f => cb1_swap_lists unit f       *)
(*   [tt] [tt])，本件泛化至任意 S/en）                                    *)
(*   判词：exact 一击收编，出转发定理 cms_bs_swap。                         *)
(*                                                                       *)
(* 【槽⑧】UpReqConcMixSel.v:772 sum_eq_list                               *)
(*   原语句：forall g : S -> R, req (sumf g) (rsq_bs_list_sum g enum)      *)
(*   接线引用：CZB8 SumEqListFeed.v shim 同型（其 RI 面 idt_ 桥的 req 面   *)
(*   折叠重铸）：两折叠机器 sumd_list_sum（UpReqSumD:70）与 rsq_bs_list_   *)
(*   sum（UpReqSampling:740）逐构造子同形，列表归纳一跳缝合                 *)
(*   cms_fold_req_list_sum，再经 csm_sumf 定义性展开（=sumd_list_sum       *)
(*   处方，UpReqConcSoftmax:54）收口。                                     *)
(*   判词：折叠缝合 shim + 定义性展开收编，出转发定理 cms_sum_eq_list       *)
(*   （shim 为纯转换件，零序论内容）。                                     *)
(*                                                                       *)
(* 【邻接伴件⑨】UpReqConcMixSel.v:770 bs_abs                              *)
(*   原语句：forall a, le zero a -> req (abs a) a                         *)
(*   接线引用：UpReqConcB1.v cb1_bs_abs（Or 拆支合法走廊具体层消解件）      *)
(*   判词：exact 一击收编，出转发定理 cms_bs_abs。                          *)
(*                                                                       *)
(* 【邻接伴件⑩】UpReqConcMixSel.v:771 bs_lpc                              *)
(*   原语句：forall a b c d, lt a b -> le c d -> lt (plus a c) (plus b d)  *)
(*   接线引用：同槽①（UpReqConcB1 头注「bs_lpc 槽 = lt_plus 槽同件」）      *)
(*   判词：同件同喂，出转发定理 cms_bs_lpc。                               *)
(*                                                                       *)
(* 纪律：纯构造性；语句面全 Set 层零泄露（req/le/lt 全本库 Set 面位）；      *)
(*   纯项模式（exact 直供 + 列表归纳一跳，零重写战术）；转发件全 Defined    *)
(*   收束可提取；原树零改，自建 .vo 留 side 根永不出本地。                  *)
(* ===================================================================== *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqSumD.
Require Import UpReqConcSoftmax.
Require Import UpReqSampling.
Require Import UpReqConcMixSel.
Require Import UpReqConcB1.
From Stdlib Require Import List.
Import RealInterfaceEnhancedMod.

(* 世界钉柯西 Real 实数面（lt_plus 供体 real_lt_plus_compat_lt_le 为      *)
(* S07 Real 层成品；cb1_mixing_cert 同款 RealEnhancedReal 实例）           *)

(* ============ 槽①/②：lt_plus_compat_lt_le ×2（Real 层成品直喂） ========= *)

Theorem cms_lt_plus_compat_lt_le_sel :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  assert (Hcd' : real_le c d) by exact Hcd.
  unfold real_le in Hcd'.
  destruct Hcd' as [Hlt | Heq].
  - exact (real_lt_plus_compat a b c d Hab Hlt).
  - apply (real_eq_lt_lt (plus a c) (plus a d) (plus b d)).
    + apply (RealSetoid.real_eq_plus_compat a c a d).
      * apply real_eq_refl.
      * exact Heq.
    + apply (real_eq_lt_lt (plus a d) (plus d a) (plus b d)).
      * apply real_plus_comm.
      * apply (real_lt_eq_lt (plus d a) (plus d b) (plus b d)).
        -- apply (real_lt_plus_translate d a b Hab).
        -- apply real_plus_comm.
Defined.

Theorem cms_lt_plus_compat_lt_le_time :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  assert (Hcd' : real_le c d) by exact Hcd.
  unfold real_le in Hcd'.
  destruct Hcd' as [Hlt | Heq].
  - exact (real_lt_plus_compat a b c d Hab Hlt).
  - apply (real_eq_lt_lt (plus a c) (plus a d) (plus b d)).
    + apply (RealSetoid.real_eq_plus_compat a c a d).
      * apply real_eq_refl.
      * exact Heq.
    + apply (real_eq_lt_lt (plus a d) (plus d a) (plus b d)).
      * apply real_plus_comm.
      * apply (real_lt_eq_lt (plus d a) (plus d b) (plus b d)).
        -- apply (real_lt_plus_translate d a b Hab).
        -- apply real_plus_comm.
Defined.

(* ============ 槽③-⑥：sum 四槽（csm_sumf 折叠键，任意 S/en 泛型） ======== *)

Theorem cms_sum_ext : forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
  (forall s : S0, req (f s) (g s)) -> req (csm_sumf S0 en f) (csm_sumf S0 en g).
Proof.
  intros S0 en f g H.
  unfold csm_sumf.
  induction en as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (f x) (g x) (sumd_list_sum S0 f t)
             (sumd_list_sum S0 g t) (H x) IH).
Defined.

Theorem cms_sum_linear :
  forall (S0 : Set) (en : list S0) (a : Real) (f : S0 -> Real),
    req (csm_sumf S0 en (fun s : S0 => mult a (f s)))
        (mult a (csm_sumf S0 en f)).
Proof.
  intros S0 en a f.
  unfold csm_sumf.
  induction en as [| x t IH].
  - exact (req_sym (mult a zero) zero (mult_zero a)).
  - simpl.
    exact (req_sym
             (mult a (plus (f x) (sumd_list_sum S0 f t)))
             (plus (mult a (f x))
                     (sumd_list_sum S0 (fun s : S0 => mult a (f s)) t))
             (req_trans
                (mult a (plus (f x) (sumd_list_sum S0 f t)))
                (plus (mult a (f x)) (mult a (sumd_list_sum S0 f t)))
                (plus (mult a (f x))
                        (sumd_list_sum S0 (fun s : S0 => mult a (f s)) t))
                (distrib a (f x) (sumd_list_sum S0 f t))
                (req_plus_compat (mult a (f x)) (mult a (f x))
                   (mult a (sumd_list_sum S0 f t))
                   (sumd_list_sum S0 (fun s : S0 => mult a (f s)) t)
                   (req_refl (mult a (f x)))
                   (req_sym
                      (sumd_list_sum S0 (fun s : S0 => mult a (f s)) t)
                      (mult a (sumd_list_sum S0 f t)) IH)))).
Defined.

Theorem cms_sum_add :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    req (csm_sumf S0 en (fun s : S0 => plus (f s) (g s)))
        (plus (csm_sumf S0 en f) (csm_sumf S0 en g)).
Proof.
  intros S0 en f g.
  unfold csm_sumf.
  induction en as [| x t IH].
  - exact (req_sym (plus zero zero) zero (plus_zero zero)).
  - simpl.
    exact (req_trans
             (plus (plus (f x) (g x))
                     (sumd_list_sum S0 (fun s : S0 => plus (f s) (g s)) t))
             (plus (plus (f x) (g x))
                     (plus (sumd_list_sum S0 f t) (sumd_list_sum S0 g t)))
             (plus (plus (f x) (sumd_list_sum S0 f t))
                     (plus (g x) (sumd_list_sum S0 g t)))
             (req_plus_compat (plus (f x) (g x)) (plus (f x) (g x))
                (sumd_list_sum S0 (fun s : S0 => plus (f s) (g s)) t)
                (plus (sumd_list_sum S0 f t) (sumd_list_sum S0 g t))
                (req_refl (plus (f x) (g x))) IH)
             (req_sym
                (plus (plus (f x) (sumd_list_sum S0 f t))
                        (plus (g x) (sumd_list_sum S0 g t)))
                (plus (plus (f x) (g x))
                        (plus (sumd_list_sum S0 f t)
                                (sumd_list_sum S0 g t)))
                (req_plus_exchange (f x) (g x)
                   (sumd_list_sum S0 f t) (sumd_list_sum S0 g t)))).
Defined.

Theorem cms_sum_le :
  forall (S0 : Set) (en : list S0) (f g : S0 -> Real),
    (forall s : S0, le (f s) (g s)) -> le (csm_sumf S0 en f) (csm_sumf S0 en g).
Proof.
  intros S0 en f g H.
  unfold csm_sumf.
  induction en as [| x t IH].
  - exact (le_refl zero).
  - simpl.
    exact (le_plus_compat (f x) (g x) (sumd_list_sum S0 f t)
             (sumd_list_sum S0 g t) (H x) IH).
Defined.

(* ============ 槽⑧：sum_eq_list（折叠缝合 shim + 定义性展开） ============ *)

(* 两折叠机器同构 shim：sumd_list_sum 与 rsq_bs_list_sum 逐构造子同形       *)
(* （nil 支同归 zero、cons 支同为 plus 头元尾折），列表归纳一跳，           *)
(* req_plus_compat 缝合（CZB8 SumEqListFeed shim 的 req 折叠面重铸）。      *)
Lemma cms_fold_req_list_sum :
  forall (S0 : Set) (g : S0 -> Real) (l : list S0),
    req (sumd_list_sum S0 g l) (rsq_bs_list_sum S0 g l).
Proof.
  intros S0 g l.
  induction l as [| x t IH].
  - exact (req_refl zero).
  - exact (req_plus_compat (g x) (g x)
             (sumd_list_sum S0 g t) (rsq_bs_list_sum S0 g t)
             (req_refl (g x)) IH).
Defined.

Theorem cms_sum_eq_list : forall (S0 : Set) (en : list S0) (g : S0 -> Real),
  req (csm_sumf S0 en g) (rsq_bs_list_sum S0 g en).
Proof.
  intros S0 en g.
  unfold csm_sumf.
  induction en as [| x t IH].
  - exact (req_refl zero).
  - simpl.
    exact (req_plus_compat (g x) (g x) (sumd_list_sum S0 g t)
             (rsq_bs_list_sum S0 g t) (req_refl (g x)) IH).
Defined.

(* ============ 槽⑦：bs_swap（cb1 双折归纳泛型件实例化） ================== *)

Theorem cms_bs_swap :
  forall (S0 : Set) (en : list S0) (f : S0 -> S0 -> Real),
    req (csm_sumf S0 en (fun s : S0 => csm_sumf S0 en (fun s' : S0 => f s s')))
        (csm_sumf S0 en (fun s' : S0 => csm_sumf S0 en (fun s : S0 => f s s'))).
Proof.
  intros S0 en f.
  exact (cb1_swap_lists S0 f en en).
Defined.

(* ============ 邻接伴件⑨/⑩：bs_abs / bs_lpc ============================ *)

Theorem cms_bs_abs : forall a : Real, le zero a -> req (abs a) a.
Proof.
  intros a H.
  assert (H' : real_le zero a) by exact H.
  unfold real_le in H'.
  destruct H' as [Hlt | Heq].
  - exact (real_abs_pos_req a Hlt).
  - exact (real_eq_trans (real_abs a) zero a
             (real_eq_trans (real_abs a) (real_abs zero) zero
                (real_abs_eq_compat a zero (real_eq_sym zero a Heq))
                real_abs_zero_req)
             Heq).
Defined.

Theorem cms_bs_lpc :
  forall a b c d : Real, lt a b -> le c d -> lt (plus a c) (plus b d).
Proof.
  intros a b c d Hab Hcd.
  assert (Hcd' : real_le c d) by exact Hcd.
  unfold real_le in Hcd'.
  destruct Hcd' as [Hlt | Heq].
  - exact (real_lt_plus_compat a b c d Hab Hlt).
  - apply (real_eq_lt_lt (plus a c) (plus a d) (plus b d)).
    + apply (RealSetoid.real_eq_plus_compat a c a d).
      * apply real_eq_refl.
      * exact Heq.
    + apply (real_eq_lt_lt (plus a d) (plus d a) (plus b d)).
      * apply real_plus_comm.
      * apply (real_lt_eq_lt (plus d a) (plus d b) (plus b d)).
        -- apply (real_lt_plus_translate d a b Hab).
        -- apply real_plus_comm.
Defined.

(* ============ 自检段（G4 口径：逐件 Closed 实证） ===================== *)

Print Assumptions cms_lt_plus_compat_lt_le_sel.
Print Assumptions cms_lt_plus_compat_lt_le_time.
Print Assumptions cms_sum_ext.
Print Assumptions cms_sum_linear.
Print Assumptions cms_sum_add.
Print Assumptions cms_sum_le.
Print Assumptions cms_fold_req_list_sum.
Print Assumptions cms_sum_eq_list.
Print Assumptions cms_bs_swap.
Print Assumptions cms_bs_abs.
Print Assumptions cms_bs_lpc.
