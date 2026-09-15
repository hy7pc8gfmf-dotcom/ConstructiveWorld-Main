(* ============================================================ *)
(* UpReqLatbMaxList.v *)
(* *)
(* 目的： max 侧列表版格组合件（B 形扩展线）。 *)
(* 主件： latb_max_list_le_b 及其归纳形 latb_max_list_le_b_ind；latb_lt_max_list_intro。 *)
(* 依赖： CW_ConstructiveWorld_219、UpRealLeB、UpRealLeB2、UpRealLeB3、G06_BForm。 *)
(* 备注： 为逐点函数而非最小上界公理；上界参数无需稠密性或分支证书。 *)
(* ============================================================ *)

(* ============================================================ *)
(* UpReqLatbMaxList.v —— B 形扩展线 · max 侧列表版格组合件（席T19b）  *)
(*                                                                *)
(* 立项：B形扩展线仪表-20260910 §⑥3「侦察单未立项面」首项——        *)
(*   「r_max 列表面：real_r_max_le_l_eps/le_r_eps 下界件已入  *)
(*   LeB Part E（L475/482），r_max 上界格组合（max 侧同构的列表版）  *)
(*   侦察单 T4 草图未含、未立项」。本库即该面立项落盘。              *)
(*                                                                *)
(* 上游消费（全既有件，零新增前提位）：                              *)
(*   G06_BForm（T4a/T4b latb_ 十一件：二元上界格主件 latb_max_le_b、  *)
(*     严格上界引入基元 latb_lt_max_intro——本列表版的两块格胶水）；   *)
(*   UpRealLeB（Part E 下界件 real_r_max_le_l_B / real_r_max_le_r_B  *)
(*     即 ≤_B r_max 双件——本库 E.1/E.2 列表化之源；完成器           *)
(*     real_le_closure_b_one）；UpRealLeB2（real_le_b_trans F.2）；  *)
(*   UpRealLeB3（leb3_le_b_refl 运输自反）；（Real、real_max）。 *)
(*                                                                *)
(* 主结果（1 Definition + 8 Lemma，全 Set 层、零 Prop 出面）：        *)
(*   0. latb_max_list：非空列表（头 h : 尾 t）逐位 r_max 折叠——       *)
(*      fold_right real_max h t。头驱动形：零单位元前提（无 nil 案    *)
(*      需 0 ≤_B c 之类伪义务；r_max 在 系逐点 Qmax 编码的      *)
(*      点态函数，非「任意上界中的最小上界」lubs 公理——故列表上界    *)
(*      律的上界参数 c 无需稠密性/分支证书，见主件单步证）。           *)
(*   1. latb_lt_max_list_intro：严格上界引入基元（latb_min_glb 的     *)
(*      lub 面列表对偶位）——凡成员严格小于 d，折叠 max 严格小于 d。   *)
(*   2. latb_max_list_le_b：主件（上界格律列表版）——成员全 ≤_B c     *)
(*      ⟹ 折叠 max ≤_B c。max 侧 eps 槽红利同构直达：eps 恰挂        *)
(*      latb_lt_max_list_intro 结论槽 d = c+eps 内，one 完成器单步    *)
(*      闭合（对照 min 侧主件 latb_min_le_b 须完整逐点证+Q.min_dec    *)
(*      分支——不对称判据见 T4b 勘误卡，勿对偶砍半）。                 *)
(*   3. latb_max_list_le_b_ind：主件另径（逐 list 归纳 + 二元律       *)
(*      latb_max_le_b 逐位粘合）——与件 2 完成器单步径互为印证，      *)
(*      两径殊途同归（同一语句双证）。                                *)
(*   4. latb_max_list_le_l：头 ≤_B 折叠 max（real_r_max_le_l_B 的    *)
(*      列表化；归纳 + trans + r_max 右参上界件）。                    *)
(*   5. latb_max_list_le_cons_tail：同头尾扩一件，折叠 max 单调       *)
(*      （real_r_max_le_r_B 的列表化前半：旧折叠 ≤_B 扩后折叠）。      *)
(*   6. latb_max_list_le_cons_init：换头吸收，旧折叠 ≤_B max h(换头   *)
(*      折叠)（E.2 列表化主件前半；归纳轮廓 u 泛化绕开 r_max 交换面）  *)
(*   7. latb_max_list_le_prepend：前置任意一件，旧折叠 ≤_B 新折叠     *)
(*      （件 6 换形推论，零新证）。                                    *)
(*                                                                *)
(* 不对称判据如实记录（仪表 L46 + T4b 勘误卡 L24 同源）：              *)
(*   —— max 侧：eps 挂引入式结论槽内（real_lt (max l) d 的 d 位），   *)
(*      主件可 one 完成器单步（件 2 六行）；列表版红利保持——严格      *)
(*      引入件自身一次归纳封装折叠，主件不再展开列表。                  *)
(*   —— min 侧：eps 挂 min 外侧（目标 c < min l + eps），min_glb      *)
(*      结论槽无 eps 位，单步不可达，须完整逐点证（T4b 件 8 同量级）。  *)
(*      本库不建 min 列表版（未立项，勿凭对擅自动工）。                 *)
(*                                                                *)
(* 红线自检口径：                                                     *)
(*   —— 语句面全 Set 层：结论全 real_lt（sigT 见证形）/ real_le_b      *)
(*      （forall eps 型），零 Prop 泄露；前提位 In 为 stdlib 既有      *)
(*      Prop 谓词，仅作全称前提位传递（构造 In 见证合法，全程零       *)
(*      Prop 消去入 Set——无 Or/In 分支拆除）。                         *)
(*   —— 前提位零新增；全件真证闭合无降级；禁词扫描口径零命中            *)
(*      （注释同律）；提取探针 Obj.magic=0（独立小探针，验后删）。      *)
(*   —— Print Assumptions 全件 Closed（文末七连打，证据在编译日志）。  *)
(* 编译配方（cpu_guard 包装，vo 树 = ConstructiveWorld-Main/          *)
(* ConstructiveWorld_vo，前置 .vo 121 件全族在树）：                   *)

(* ============================================================ *)

From Stdlib Require Import List.
Require Import CW_ConstructiveWorld_219.
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.
Require Import G06_BForm.

(* ============================================================ *)
(* 一、折叠定义与展开引理                                              *)
(* ============================================================ *)

(* 件 0：非空列表逐位 r_max 折叠：头 h 为初值，尾 t 逐件 r_max 并入。
   头驱动形使 nil 案不存在（真空表无 max——构造性诚实形），
   故上界格律与下界伴随件均无需单位元前提。 *)
Definition latb_max_list (h : Real) (t : list Real) : Real :=
  fold_right real_max h t.

(* 展开引理：折叠步进形（后续各件 change 换形用，免依赖 simpl 折叠
   的再折叠行为）。两向各为 delta+iota 可逆换形。 *)
Lemma latb_max_list_cons_eq :
  forall (h w : Real) (t : list Real),
    Id (latb_max_list h (w :: t)) (real_max w (latb_max_list h t)).
Proof.
  intros h w t. unfold latb_max_list. simpl. apply id_refl.
Qed.

(* ============================================================ *)
(* 二、严格上界引入基元（lub 面）与上界格律主件                          *)
(* ============================================================ *)

(* 件 1：严格上界引入：凡成员 x <ᴮ d，则折叠 max l <ᴮ d。
   逐 list 归纳 + 二元基元 latb_lt_max_intro 粘合；nil 案即头自身
   严格界（头驱动形免单位元义务）。对偶位注记：此为 latb_min_glb
   （T4b 件 7，glb 面：p<成分 ⟹ p<min）的 max/lub 镜像，eps 槽
   即本件结论 d 位——主件红利之源。 *)
Lemma latb_lt_max_list_intro : forall (h : Real) (t : list Real) (d : Real),
  (forall x : Real, In x (h :: t) -> real_lt x d) ->
  real_lt (latb_max_list h t) d.
Proof.
  intros h t d H. induction t as [| w rest IH].
  - exact (H h (in_eq h nil)).
  - change (real_lt (real_max w (latb_max_list h rest)) d).
    apply latb_lt_max_intro.
    + exact (H w (in_cons h w (w :: rest) (in_eq w rest))).
    + apply IH. intros x Hx.
      assert (Hx2 : In x (h :: w :: rest)).
      { destruct Hx as [He | Hr].
        - left. exact He.
        - right. right. exact Hr. }
      exact (H x Hx2).
Qed.

(* 件 2（主件）：上界格律列表版：成员全 ≤_B c ⟹ 折叠 max ≤_B c。
   max 侧同构单步：给 eps>0，成员界同取 d := c+eps（real_le_b 展开
   即逐成员严格界），件 1 一步得折叠 max < c+eps，Or 左支入精确面，
   one 完成器单步完成——无需 eps 拆分、无需列表展开（归纳封装在
   件 1 内），与二元主件 latb_max_le_b 同为六行形。 *)
Lemma latb_max_list_le_b : forall (h : Real) (t : list Real) (c : Real),
  (forall x : Real, In x (h :: t) -> real_le_b x c) ->
  real_le_b (latb_max_list h t) c.
Proof.
  intros h t c H.
  apply real_le_closure_b_one. intros eps Heps. unfold real_le. left.
  apply latb_lt_max_list_intro. intros x Hx.
  exact (H x Hx eps Heps).
Qed.

(* 件 3（主件另径）：逐 list 归纳 + 二元律逐位粘合。
   与件 2 同语句双证：nil 案头界直取；cons 案二元 latb_max_le_b
   两支（新头界 + IH 尾折叠界）。两径互为印证，主件以件 2 为正身。 *)
Lemma latb_max_list_le_b_ind : forall (h : Real) (t : list Real) (c : Real),
  (forall x : Real, In x (h :: t) -> real_le_b x c) ->
  real_le_b (latb_max_list h t) c.
Proof.
  intros h t c H. induction t as [| w rest IH].
  - exact (H h (in_eq h nil)).
  - change (real_le_b (real_max w (latb_max_list h rest)) c).
    apply latb_max_le_b.
    + exact (H w (in_cons h w (w :: rest) (in_eq w rest))).
    + apply IH. intros x Hx.
      assert (Hx2 : In x (h :: w :: rest)).
      { destruct Hx as [He | Hr].
        - left. exact He.
        - right. right. exact Hr. }
      exact (H x Hx2).
Qed.

(* ============================================================ *)
(* 三、下界伴随件（E.1/E.2 列表化：成员位 ≤_B 折叠 max）                *)
(* ============================================================ *)

(* 件 4：头 ≤_B 折叠 max（real_r_max_le_l_B 的列表化）。
   归纳：nil 案自反；cons 案 h ≤_B 尾折叠（IH）≤_B 含新头折叠
   （r_max 右参上界件 real_r_max_le_r_B）。 *)
Lemma latb_max_list_le_l : forall (h : Real) (t : list Real),
  real_le_b h (latb_max_list h t).
Proof.
  intros h t. induction t as [| w rest IH].
  - apply leb3_le_b_refl.
  - change (real_le_b h (real_max w (latb_max_list h rest))).
    apply (real_le_b_trans h (latb_max_list h rest)).
    + exact IH.
    + apply real_r_max_le_r_B.
Qed.

(* 件 5：同头尾扩一件：折叠 max(h::t) ≤_B 折叠 max(h::u::t)。
   real_r_max_le_r_B 的列表化前半。归纳 + 二元律粘合：
   新头 v 支经 r_max 左参上界件 + 右参抬升；尾折叠支经 IH
   （v::rest 与 u::rest 同头 h）+ 右参抬升。 *)
Lemma latb_max_list_le_cons_tail : forall (h u : Real) (t : list Real),
  real_le_b (latb_max_list h t) (latb_max_list h (u :: t)).
Proof.
  intros h u t. revert h u. induction t as [| v rest IH]; intros h u.
  - change (real_le_b h (real_max u h)). apply real_r_max_le_r_B.
  - change (real_le_b (real_max v (latb_max_list h rest))
             (real_max u (real_max v (latb_max_list h rest)))).
    apply latb_max_le_b.
    + apply (real_le_b_trans v (real_max v (latb_max_list h rest))).
      * apply real_r_max_le_l_B.
      * apply real_r_max_le_r_B.
    + apply (real_le_b_trans (latb_max_list h rest)
               (real_max v (latb_max_list h rest))).
      * exact (IH h v).
      * apply real_r_max_le_r_B.
Qed.

(* 件 6：换头吸收：折叠 max(h::t) ≤_B max h（折叠 max(x::t)）。
   E.2（b ≤_B max a b）列表化主件前半。cons 案二元律两支：
   新头 u 支经 r_max 左参上界 + 右参抬升两步；旧折叠支经 IH
   （换头 x 后同 h 路径）+ 右参同头单调抬升（二元律两次喂入）。
   全程零 comm 依赖——r_max 交换面在 无直连件，本库
   以归纳轮廓（u 连同 h 一起泛化）绕开，不立交换桥。 *)
Lemma latb_max_list_le_cons_init : forall (h x : Real) (t : list Real),
  real_le_b (latb_max_list h t) (real_max h (latb_max_list x t)).
Proof.
  intros h x t. revert x. induction t as [| u rest IH]; intros x.
  - change (real_le_b h (real_max h x)). apply real_r_max_le_l_B.
  - change (real_le_b (real_max u (latb_max_list h rest))
             (real_max h (real_max u (latb_max_list x rest)))).
    apply latb_max_le_b.
    + apply (real_le_b_trans u (real_max u (latb_max_list x rest))).
      * apply real_r_max_le_l_B.
      * apply real_r_max_le_r_B.
    + apply (real_le_b_trans (latb_max_list h rest)
               (real_max h (latb_max_list x rest))).
      * exact (IH x).
      * apply latb_max_le_b.
        { apply real_r_max_le_l_B. }
        { apply (real_le_b_trans (latb_max_list x rest)
                   (real_max u (latb_max_list x rest))).
          { apply real_r_max_le_r_B. }
          { apply real_r_max_le_r_B. } }
Qed.

(* 件 7：前置扩张：折叠 max(h::t) ≤_B 折叠 max(x::h::t)。
   件 6 的换形推论（零新证）：fold_right 嵌套形下
   latb_max_list x (h::t) 折叠即 real_max h (latb_max_list x t)。 *)
Lemma latb_max_list_le_prepend : forall (x h : Real) (t : list Real),
  real_le_b (latb_max_list h t) (latb_max_list x (h :: t)).
Proof.
  intros x h t. exact (latb_max_list_le_cons_init h x t).
Qed.

(* ============================================================ *)
(* 四、假设审计（全件 Closed，证据在编译日志）                           *)
(* ============================================================ *)

Print Assumptions latb_max_list.
Print Assumptions latb_max_list_cons_eq.
Print Assumptions latb_lt_max_list_intro.
Print Assumptions latb_max_list_le_b.
Print Assumptions latb_max_list_le_b_ind.
Print Assumptions latb_max_list_le_l.
Print Assumptions latb_max_list_le_cons_tail.
Print Assumptions latb_max_list_le_cons_init.
Print Assumptions latb_max_list_le_prepend.
