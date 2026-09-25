(* ============================================================ *)
(* UpReqMisc5B.v —— 希尔伯特空间正交分解的 req 层构造件。         *)
(*                                                              *)
(* 使命： 本件形式化希尔伯特空间正交分解（存在性/唯一性）、       *)
(*   Gram-Schmidt 步与多变量可微代数面的 req（setoid 层）伴生族。 *)
(*                                                              *)
(* 依赖： CW_ConstructiveWorld_219、UpReqAlgebra、UpReqMisc5。    *)
(* 构造性： 状态空间与希尔伯特结构为显式节假设申报前提；投影幂等性 *)
(*   为显式申报；核心件全 Qed；纯 term-mode 组装；可提取。        *)
(* 编译配方： 9.1 直调（toolchain env.sh 同源）、cpu_guard 绑核。 *)
(*                                                              *)
(* 对标： mathlib 内积空间正交投影存在性的对应物；               *)
(*   本库自建于 req 接口层。                                     *)
(*                                                              *)
(* 接口申报： 节内假设申报三位——rprojection_idempotent（本簇     *)
(*   未依存，源模块接口同位保留）；rmv_adjoint（未使用，同位     *)
(*   保留）；rop_lipschitz（被 req_op_lipschitz_compose 使用）。 *)
(*                                                              *)
(* 编目： Part A 正交分解 2 件；Part B Gram-Schmidt 4 件；        *)
(*   Part C 多变量代数面 14 件。等号位分派：R 值位等号 req；     *)
(*   向量载体位等号 Id（req 接口字段仅定义在 R 上——载体无       *)
(*   setoid 等位可迁，Id 即归纳族构造性等号）。                  *)
(*                                                              *)
(* ============================================================ *)

(* ============================================================ *)
(* 覆盖核对（req 件名 ← Id 源件名，逐件同名换前缀）：             *)
(*   Hilbert：req_orthogonal_decomposition_exists / _unique；     *)
(*   GramSchmidt：req_inner_sopp_l / req_inner_szero_l /          *)
(*     req_gram_schmidt_step / req_gram_schmidt_pair；            *)
(*   Multivar：req_inner_splus_r / req_mv_compose_diff_decomp 等  *)
(*     14 件（件名见文内各横幅）。                                *)
(* ============================================================ *)

(* 向量世界依存簇（Hilbert/GramSchmidt/Multivar）的 req 层伴生：  *)
(*                                                              *)
(*   类转写层（reqStateSpace/reqStateSpaceExt/reqHilbertSpace/    *)
(*   reqSumOver）已随 UpReqMisc5.v Part 0 在案，本件 Require 依存。 *)
(*                                                              *)
(* 等号位分派：R 值位等号 req；向量载体位等号 Id——req 接口        *)
(*   字段仅定义在 R 上，载体无 setoid 等位可迁，Id 即归纳族构造性  *)
(*   等号。                                                       *)
(*                                                              *)
(* Id 级 list/nat 事实在 req 目标内的运送用 match-in-return 组合器 *)
(*   （零改写战术；whole : P b（index 侧）、分支 pf : P a（参数    *)
(*   侧）——方向纪律如上）。                                       *)
(*                                                              *)
(* 诚实边界登记表：                                               *)
(*                                                              *)
(*   1. rprojection_idempotent：源模块投影幂等位同构；本簇未依存， *)
(*      源模块接口同位保留（未使用位，纯删不改语句面，按同位副本   *)
(*      纪律保留）。                                              *)
(*   2. rmv_adjoint：伴随存在位同构；未使用，同位保留（理由同上）。*)
(*   3. rop_lipschitz：算子范数界位；被 req_op_lipschitz_compose  *)
(*      使用（sigT N + 0 ≤ N + 逐点上界）。                       *)
(*                                                              *)
(*   加位判读：op_lipschitz_compose 的 Id 证明实际只依存           *)
(*      le_mult_compat_weak/mult_zero 接口字段 + op_lipschitz     *)
(*      自带假设位，零新增假设位。                                *)
(*                                                              *)
(* 提取面：多态核件提取 Obj.magic=0（独立检验文件验证）。         *)
(*                                                              *)
(* ============================================================ *)

Require Import CW_ConstructiveWorld_219.
Require Import UpReqAlgebra.
Require Import UpReqMisc5.
Import RealInterfaceEnhancedMod.
From Stdlib Require Import List.
Import ListNotations.

(* ============================================================ *)
(* Part A：HilbertTheorems 2 件（Id L1281-1400 依存面）           *)
(* ============================================================ *)
Section ReqHilbertTheorems.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {SS : reqStateSpace R RIS} {HS : reqHilbertSpace R RIS SS}.

(* 正交残差存在性（Id orthogonal_decomposition_exists L1306）：
   w := v − proj u v 的 sigT 见证；⟨w,u⟩=0（proj_orthogonal 字段 sym 换位）
   + v = proj u v + w（向量 Id 代数链） *)
Theorem req_orthogonal_decomposition_exists :
  forall u v : @rSS R RIS SS,
    sigT (fun w : @rSS R RIS SS =>
      And (@req R RIS (rinner u w) (@zero R RIS))
          (Id v (@rsplus R RIS SS (rproj u v) w))).
Proof.
  intros u v.
  exists (@rsplus R RIS SS v (@rsopp R RIS SS (rproj u v))).
  split.
  - exact (req_trans _ _ _
            (req_sym _ _ (rinner_sym (rsplus v (rsopp (rproj u v))) u))
            (rproj_orthogonal u v)).
  - (* v = proj u v + (v − proj u v)：splus 代数（Id 向量链） *)
    assert (Hopp : Id (@rsplus R RIS SS (rproj u v)
                                  (@rsplus R RIS SS v (@rsopp R RIS SS (rproj u v))))
                      (@rsplus R RIS SS (rproj u v)
                                  (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v)) v)))
      by exact (id_cong (fun x => @rsplus R RIS SS (rproj u v) x)
                        (rsplus_comm v (@rsopp R RIS SS (rproj u v)))).
    assert (Hassoc : Id (@rsplus R RIS SS (rproj u v)
                                    (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v)) v))
                        (@rsplus R RIS SS (@rsplus R RIS SS (rproj u v)
                                                     (@rsopp R RIS SS (rproj u v))) v))
      by exact (rsplus_assoc (rproj u v) (@rsopp R RIS SS (rproj u v)) v).
    assert (Hinv : Id (@rsplus R RIS SS (rproj u v) (@rsopp R RIS SS (rproj u v)))
                      (@rszero R RIS SS))
      by exact (rsplus_opp (rproj u v)).
    assert (Hzero : Id (@rsplus R RIS SS (@rszero R RIS SS) v) v)
      by exact (id_trans (rsplus_comm (@rszero R RIS SS) v) (rsplus_zero v)).
    exact (id_sym (id_trans Hopp (id_trans Hassoc
              (id_trans (id_cong (fun x => @rsplus R RIS SS x v) Hinv) Hzero)))).
Qed.

(* 正交分解唯一性（Id orthogonal_decomposition_unique L1344）：
   投影的几何确定性——向量 Id 代数（左加 sopp p 折叠） *)
Theorem req_orthogonal_decomposition_unique :
  forall (u v w1 w2 : @rSS R RIS SS),
    @req R RIS (rinner w1 u) (@zero R RIS) ->
    Id v (@rsplus R RIS SS (rproj u v) w1) ->
    @req R RIS (rinner w2 u) (@zero R RIS) ->
    Id v (@rsplus R RIS SS (rproj u v) w2) ->
    Id w1 w2.
Proof.
  intros u v w1 w2 _ Hv1 _ Hv2.
  assert (Heq : Id (@rsplus R RIS SS (rproj u v) w1) (@rsplus R RIS SS (rproj u v) w2))
    by exact (id_trans (id_sym Hv1) Hv2).
  assert (Hc : Id (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                   (@rsplus R RIS SS (rproj u v) w1))
                  (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                   (@rsplus R RIS SS (rproj u v) w2)))
    by exact (id_cong (fun x => @rsplus R RIS SS (@rsopp R RIS SS (rproj u v)) x) Heq).
  assert (Hl1 : Id (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                   (@rsplus R RIS SS (rproj u v) w1)) w1).
  {
    assert (H1 : Id (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                     (@rsplus R RIS SS (rproj u v) w1))
                    (@rsplus R RIS SS (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                                       (rproj u v)) w1))
      by exact (rsplus_assoc (@rsopp R RIS SS (rproj u v)) (rproj u v) w1).
    assert (H2 : Id (@rsplus R RIS SS (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                                       (rproj u v)) w1)
                    (@rsplus R RIS SS (@rszero R RIS SS) w1))
      by exact (id_cong (fun x => @rsplus R RIS SS x w1)
                        (id_trans (rsplus_comm (@rsopp R RIS SS (rproj u v)) (rproj u v))
                                  (rsplus_opp (rproj u v)))).
    assert (H3 : Id (@rsplus R RIS SS (@rszero R RIS SS) w1) w1)
      by exact (id_trans (rsplus_comm (@rszero R RIS SS) w1) (rsplus_zero w1)).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  assert (Hl2 : Id (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                   (@rsplus R RIS SS (rproj u v) w2)) w2).
  {
    assert (H1 : Id (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                     (@rsplus R RIS SS (rproj u v) w2))
                    (@rsplus R RIS SS (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                                       (rproj u v)) w2))
      by exact (rsplus_assoc (@rsopp R RIS SS (rproj u v)) (rproj u v) w2).
    assert (H2 : Id (@rsplus R RIS SS (@rsplus R RIS SS (@rsopp R RIS SS (rproj u v))
                                                       (rproj u v)) w2)
                    (@rsplus R RIS SS (@rszero R RIS SS) w2))
      by exact (id_cong (fun x => @rsplus R RIS SS x w2)
                        (id_trans (rsplus_comm (@rsopp R RIS SS (rproj u v)) (rproj u v))
                                  (rsplus_opp (rproj u v)))).
    assert (H3 : Id (@rsplus R RIS SS (@rszero R RIS SS) w2) w2)
      by exact (id_trans (rsplus_comm (@rszero R RIS SS) w2) (rsplus_zero w2)).
    exact (id_trans H1 (id_trans H2 H3)).
  }
  exact (id_trans (id_sym Hl1) (id_trans Hc Hl2)).
Qed.

End ReqHilbertTheorems.

(* ============================================================ *)
(* Part B：GramSchmidt 4 件（Id L24738-24900 依存面；              *)
(*         StateSpaceExtended 面 = reqStateSpaceExt）             *)
(* ============================================================ *)
Section ReqGramSchmidt.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {SSE : reqStateSpaceExt R RIS}
        {HS : reqHilbertSpace R RIS (@rsse_base R RIS SSE)}.

Let SSx : reqStateSpace R RIS := @rsse_base R RIS SSE.
Local Existing Instance SSx.

(* Id projection_idempotent L24840 诚实假设位同构（本簇未依存，源模块接口同位保留） *)
Variable rprojection_idempotent : forall u v : @rSS R RIS SSx,
  Id (rproj u (rproj u v)) (rproj u v).

(* Id inner_sopp_l L24791：⟨−x, y⟩ = −⟨x,y⟩（R 值位 req；
   smult_opp 桥的 Id 部分以 match 组合器入 req 链，零改写战术） *)
Lemma req_inner_sopp_l : forall x y : @rSS R RIS SSx,
  @req R RIS (rinner (rsopp x) y) (opp (rinner x y)).
Proof.
  intros x y.
  assert (Hsm : Id (rsmult (opp one) x) (rsopp (rsmult one x)))
    by exact (rsmult_opp one x).
  assert (Hone : Id (rsmult one x) x)
    by exact (rsmult_one x).
  assert (Hsopp : Id (rsmult (opp one) x) (rsopp x))
    by exact (id_trans Hsm (id_cong rsopp Hone)).
  exact (req_trans _ _ _
    (match Hsopp in (Id _ z) return
        (req (rinner z y) (rinner (rsmult (opp one) x) y))
     with id_refl => req_refl _ end)
    (req_trans _ _ _
      (rinner_smult_l (opp one) x y)
      (req_trans _ _ _
        (req_opp_mult_r one (rinner x y))
        (req_opp_compat (mult one (rinner x y)) (rinner x y)
                        (req_mult_one_l (rinner x y)))))).
Qed.

(* Id inner_szero_l L24812：⟨0, y⟩ = 0（splus_opp + inner_splus_l + inner_sopp_l） *)
Lemma req_inner_szero_l : forall y : @rSS R RIS SSx,
  @req R RIS (rinner rszero y) (zero).
Proof.
  intro y.
  assert (Hz : Id (rsplus y (rsopp y)) rszero)
    by exact (rsplus_opp y).
  exact (req_trans _ _ _
    (match Hz in (Id _ z) return (req (rinner z y) (rinner (rsplus y (rsopp y)) y))
     with id_refl => req_refl _ end)
    (req_trans _ _ _
      (rinner_splus_l y (rsopp y) y)
      (req_trans _ _ _
        (req_plus_compat (rinner y y) (rinner y y)
                         (rinner (rsopp y) y) (opp (rinner y y))
                         (req_refl (rinner y y)) (req_inner_sopp_l y y))
        (plus_opp (rinner y y))))).
Qed.

(* Id gram_schmidt_step L24844：w := v − proj u v 的正交分量 sigT 见证 *)
Theorem req_gram_schmidt_step : forall u v : @rSS R RIS SSx,
  Not (Id u rszero) ->
  sigT (fun w : @rSS R RIS SSx =>
    And (req (rinner u w) zero)
        (Id v (rsplus (rproj u v) w))).
Proof.
  intros u v Hu.
  exists (rsplus v (rsopp (rproj u v))).
  split.
  - exact (req_trans _ _ _
            (req_sym _ _ (rinner_sym (rsplus v (rsopp (rproj u v))) u))
            (rproj_orthogonal u v)).
  - assert (Hopp : Id (rsplus (rproj u v) (rsplus v (rsopp (rproj u v))))
                      (rsplus (rproj u v) (rsplus (rsopp (rproj u v)) v)))
      by exact (id_cong (fun x => rsplus (rproj u v) x)
                        (rsplus_comm v (rsopp (rproj u v)))).
    assert (Hassoc : Id (rsplus (rproj u v) (rsplus (rsopp (rproj u v)) v))
                        (rsplus (rsplus (rproj u v) (rsopp (rproj u v))) v))
      by exact (rsplus_assoc (rproj u v) (rsopp (rproj u v)) v).
    assert (Hinv : Id (rsplus (rproj u v) (rsopp (rproj u v))) rszero)
      by exact (rsplus_opp (rproj u v)).
    assert (Hzero : Id (rsplus rszero v) v)
      by exact (id_trans (rsplus_comm rszero v) (rsplus_zero v)).
    exact (id_sym (id_trans Hopp (id_trans Hassoc
              (id_trans (id_cong (fun x => rsplus x v) Hinv) Hzero)))).
Qed.

(* Id gram_schmidt_pair L24874（孪生命名件） *)
Theorem req_gram_schmidt_pair : forall u v : @rSS R RIS SSx,
  Not (Id u rszero) ->
  sigT (fun w : @rSS R RIS SSx =>
    And (req (rinner u w) zero)
        (Id v (rsplus (rproj u v) w))).
Proof.
  intros u v Hu.
  exact (req_gram_schmidt_step u v Hu).
Qed.

End ReqGramSchmidt.

(* ============================================================ *)
(* Part C：MultivariableDifferentiable 代数面 14 件               *)
(* （Id L26686-27500；DifferentiableMV/MVVec 记录簇） *)
(* ============================================================ *)
Section ReqMultivar.
Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}.
Context {SSE : reqStateSpaceExt R RIS}
        {HS : reqHilbertSpace R RIS (@rsse_base R RIS SSE)}.

Let SSx : reqStateSpace R RIS := @rsse_base R RIS SSE.
Local Existing Instance SSx.

(* Id inner_splus_r L26722：⟨x, y+z⟩ = ⟨x,y⟩ + ⟨x,z⟩（sym 换位 ×2） *)
Lemma req_inner_splus_r : forall x y z : @rSS R RIS SSx,
  req (rinner x (rsplus y z)) (plus (rinner x y) (rinner x z)).
Proof.
  intros x y z.
  assert (H1 : req (rinner x (rsplus y z)) (rinner (rsplus y z) x))
    by exact (rinner_sym x (rsplus y z)).
  assert (H2 : req (rinner (rsplus y z) x) (plus (rinner y x) (rinner z x)))
    by exact (rinner_splus_l y z x).
  assert (H3 : req (plus (rinner y x) (rinner z x)) (plus (rinner x y) (rinner x z)))
    by exact (req_plus_compat _ _ _ _ (rinner_sym y x) (rinner_sym z x)).
  exact (req_trans _ _ _ H1 (req_trans _ _ _ H2 H3)).
Qed.

(* Id mv_compose_diff_decomp L26739（复用 UpReqMisc5 req_compose_diff_decomp；
   D := X、h := one 特化 + mult_one 换形） *)
Lemma req_mv_compose_diff_decomp : forall (A B C G g0 X : R),
  req (req_minus A (plus B (mult C X)))
     (plus (req_minus A (plus B (mult C (req_minus G g0))))
           (mult C (req_minus (req_minus G g0) X))).
Proof.
  intros A B C G g0 X.
  assert (H1 : req (req_minus A (plus B (mult (mult C X) one)))
                   (plus (req_minus A (plus B (mult C (req_minus G g0))))
                         (mult C (req_minus (req_minus G g0) (mult X one)))))
    by exact (req_compose_diff_decomp A B C X G g0 one).
  (* 左参数位：(mult C X)·one → C·X（mult_assoc 反向 + mult_one） *)
  assert (Hm0 : req (mult (mult C X) one) (mult C X))
    by exact (req_trans _ _ _
              (req_sym _ _ (mult_assoc C X one))
              (req_mult_compat C C (mult X one) X (req_refl C) (mult_one X))).
  assert (Hm1 : req (plus B (mult (mult C X) one)) (plus B (mult C X)))
    by exact (req_plus_compat B B (mult (mult C X) one) (mult C X) (req_refl B) Hm0).
  assert (Hl : req (req_minus A (plus B (mult (mult C X) one)))
                   (req_minus A (plus B (mult C X)))).
  { unfold req_minus.
    exact (req_plus_compat A A (opp (plus B (mult (mult C X) one))) (opp (plus B (mult C X)))
                           (req_refl A)
                           (req_opp_compat (plus B (mult (mult C X) one))
                                           (plus B (mult C X)) Hm1)). }
  (* 右参数位：mult X one → X 于 req_minus 内（unfold + opp 换形） *)
  assert (Hsub : req (plus (req_minus G g0) (opp (mult X one)))
                     (plus (req_minus G g0) (opp X)))
    by exact (req_plus_compat (req_minus G g0) (req_minus G g0)
                              (opp (mult X one)) (opp X)
                              (req_refl (req_minus G g0))
                              (req_opp_compat (mult X one) X (mult_one X))).
  unfold req_minus.
  assert (Hr : req (plus (req_minus A (plus B (mult C (req_minus G g0))))
                         (mult C (plus (req_minus G g0) (opp (mult X one)))))
                    (plus (req_minus A (plus B (mult C (req_minus G g0))))
                          (mult C (plus (req_minus G g0) (opp X))))).
  { exact (req_plus_compat (req_minus A (plus B (mult C (req_minus G g0))))
                           (req_minus A (plus B (mult C (req_minus G g0))))
                           (mult C (plus (req_minus G g0) (opp (mult X one))))
                           (mult C (plus (req_minus G g0) (opp X)))
                           (req_refl (req_minus A (plus B (mult C (req_minus G g0)))))
                           (req_mult_compat C C (plus (req_minus G g0) (opp (mult X one)))
                                            (plus (req_minus G g0) (opp X))
                                            (req_refl C) Hsub)). }
  exact (req_trans _ _ _ (req_sym _ _ Hl) (req_trans _ _ _ H1 Hr)).
Qed.

(* Id inner_smult_r L27228：⟨x, a·y⟩ = a·⟨x,y⟩（inner_smult_l + sym 换位） *)
Lemma req_inner_smult_r : forall (a : R) (x y : @rSS R RIS SSx),
  req (rinner x (rsmult a y)) (mult a (rinner x y)).
Proof.
  intros a x y.
  assert (H1 : req (rinner x (rsmult a y)) (rinner (rsmult a y) x))
    by exact (rinner_sym x (rsmult a y)).
  assert (H2 : req (rinner (rsmult a y) x) (mult a (rinner y x)))
    by exact (rinner_smult_l a y x).
  assert (H3 : req (mult a (rinner y x)) (mult a (rinner x y)))
    by exact (req_mult_compat a a (rinner y x) (rinner x y)
                             (req_refl a) (rinner_sym y x)).
  exact (req_trans _ _ _ H1 (req_trans _ _ _ H2 H3)).
Qed.

(* Id inner_sopp_r L27242：⟨x, −y⟩ = −⟨x,y⟩（smult_opp + inner_smult_r） *)
Lemma req_inner_sopp_r : forall x y : @rSS R RIS SSx,
  req (rinner x (rsopp y)) (opp (rinner x y)).
Proof.
  intros x y.
  assert (Hsm : Id (rsmult (opp one) y) (rsopp (rsmult one y)))
    by exact (rsmult_opp one y).
  assert (Hone : Id (rsmult one y) y)
    by exact (rsmult_one y).
  assert (Hsopp : Id (rsmult (opp one) y) (rsopp y))
    by exact (id_trans Hsm (id_cong rsopp Hone)).
  exact (req_trans _ _ _
    (match id_sym Hsopp in (Id _ z) return
        (req (rinner x (rsopp y)) (rinner x z))
     with id_refl => req_refl _ end)
    (req_trans _ _ _
      (req_inner_smult_r (opp one) x y)
      (req_trans _ _ _
        (req_opp_mult_r one (rinner x y))
        (req_opp_compat (mult one (rinner x y)) (rinner x y)
                        (req_mult_one_l (rinner x y)))))).
Qed.

(* Id inner_sminus_r L27261：⟨x, u−v⟩ = ⟨x,u⟩ − ⟨x,v⟩ *)
Lemma req_inner_sminus_r : forall x u v : @rSS R RIS SSx,
  req (rinner x (@rsminus R RIS SSx u v)) (req_minus (rinner x u) (rinner x v)).
Proof.
  intros x u v.
  unfold req_minus.
  exact (req_trans _ _ _    (req_inner_splus_r x u (rsopp v))    (req_plus_compat (rinner x u) (rinner x u)                     (rinner x (rsopp v)) (opp (rinner x v))                     (req_refl (rinner x u)) (req_inner_sopp_r x v))).
Qed.

(* Id splus_sminus_cancel L27272：a + (b − a) = b（向量 Id 链） *)
Lemma req_splus_sminus_cancel : forall a b : @rSS R RIS SSx,
  Id (rsplus a (@rsminus R RIS SSx b a)) b.
Proof.
  intros a b.
  unfold rsminus.
  assert (H1 : Id (rsplus a (rsplus b (rsopp a))) (rsplus a (rsplus (rsopp a) b)))
    by exact (id_cong (fun z => rsplus a z) (rsplus_comm b (rsopp a))).
  assert (H2 : Id (rsplus a (rsplus (rsopp a) b)) (rsplus (rsplus a (rsopp a)) b))
    by exact (rsplus_assoc a (rsopp a) b).
  assert (H3 : Id (rsplus (rsplus a (rsopp a)) b) (rsplus rszero b))
    by exact (id_cong (fun z => rsplus z b) (rsplus_opp a)).
  assert (H4 : Id (rsplus rszero b) b)
    by exact (id_trans (rsplus_comm rszero b) (rsplus_zero b)).
  exact (id_trans H1 (id_trans H2 (id_trans H3 H4))).
Qed.

(* Id sopp_szero L27290：−0 = 0（向量 Id 链） *)
Lemma req_sopp_szero : Id (rsopp rszero) rszero.
Proof.
  assert (H1 : Id (rsopp rszero) (rsplus (rsopp rszero) rszero))
    by exact (id_sym (rsplus_zero (rsopp rszero))).
  assert (H2 : Id (rsplus (rsopp rszero) rszero) (rsplus rszero (rsopp rszero)))
    by exact (rsplus_comm (rsopp rszero) rszero).
  assert (H3 : Id (rsplus rszero (rsopp rszero)) rszero)
    by exact (rsplus_opp rszero).
  exact (id_trans H1 (id_trans H2 H3)).
Qed.

(* Id sminus_sminus_szero L27308：(u−v) − 0 = u−v（向量 Id 链） *)
Lemma req_sminus_sminus_szero : forall u v : @rSS R RIS SSx,
  Id (@rsminus R RIS SSx (@rsminus R RIS SSx u v) rszero) (@rsminus R RIS SSx u v).
Proof.
  intros u v.
  unfold rsminus.
  exact (id_trans (id_cong (fun z => rsplus (rsplus u (rsopp v)) z) req_sopp_szero)                  (rsplus_zero (rsplus u (rsopp v)))).
Qed.

(* Id smetric_sminus_zero L27324：度量平移不变（smetric_snorm +
   sminus_sminus_szero 的 Id 事实以 match 组合器入 req 链） *)
Theorem req_smetric_sminus_zero : forall u v : @rSS R RIS SSx,
  req (rsmetric (@rsminus R RIS SSx u v) rszero) (rsmetric u v).
Proof.
  intros u v.
  exact (req_trans _ _ _    (rsmetric_snorm (@rsminus R RIS SSx u v) rszero)    (req_trans _ _ _      (match req_sminus_sminus_szero u v in (Id _ z) return          (req (rsnorm (@rsminus R RIS SSx (@rsminus R RIS SSx u v) rszero)) (rsnorm z))       with id_refl => req_refl _ end)      (req_sym _ _ (rsmetric_snorm u v)))).
Qed.

(* Id inner_sminus_l L27355：⟨a−b, c⟩ = ⟨a,c⟩ − ⟨b,c⟩ *)
Lemma req_inner_sminus_l : forall a b c : @rSS R RIS SSx,
  req (rinner (@rsminus R RIS SSx a b) c) (req_minus (rinner a c) (rinner b c)).
Proof.
  intros a b c.
  unfold req_minus.
  exact (req_trans _ _ _    (rinner_splus_l a (rsopp b) c)    (req_plus_compat (rinner a c) (rinner a c)                     (rinner (rsopp b) c) (opp (rinner b c))                     (req_refl (rinner a c)) (req_inner_sopp_l b c))).
Qed.

(* Id sminus_zero_cancel L27369：a − b = 0 ⟹ a = b（向量 Id 链） *)
Lemma req_sminus_zero_cancel : forall a b : @rSS R RIS SSx,
  Id (@rsminus R RIS SSx a b) rszero -> Id a b.
Proof.
  intros a b H.
  assert (H1 : Id a (rsplus b (@rsminus R RIS SSx a b)))
    by exact (id_sym (req_splus_sminus_cancel b a)).
  exact (id_trans H1 (id_trans (id_cong (fun z => rsplus b z) H) (rsplus_zero b))).
Qed.

(* 伴随接口（Id mv_adjoint L27376 诚实假设位同构，同位保留） *)
Variable rmv_adjoint : forall (L : @rSS R RIS SSx -> @rSS R RIS SSx),
  sigT (fun Lad : @rSS R RIS SSx -> @rSS R RIS SSx => forall h w : @rSS R RIS SSx,
    req (rinner (L h) w) (rinner h (Lad w))).

(* 算子范数界（Id op_lipschitz L27384 诚实假设位同构，同位保留；
   And = Set 层乘积） *)
Variable rop_lipschitz : forall (L : @rSS R RIS SSx -> @rSS R RIS SSx),
  sigT (fun N : R => And (le zero N) (forall h : @rSS R RIS SSx,
    le (rsmetric (L h) rszero) (mult N (rsmetric h rszero)))).

(* Id mv_adjoint_unique L27383：伴随唯一（⟨h,h'⟩ = 0 ⟹ inner_definite） *)
Lemma req_mv_adjoint_unique : forall (L : @rSS R RIS SSx -> @rSS R RIS SSx)
    (Lad1 Lad2 : @rSS R RIS SSx -> @rSS R RIS SSx),
  (forall h w : @rSS R RIS SSx, req (rinner (L h) w) (rinner h (Lad1 w))) ->
  (forall h w : @rSS R RIS SSx, req (rinner (L h) w) (rinner h (Lad2 w))) ->
  forall w : @rSS R RIS SSx, Id (Lad1 w) (Lad2 w).
Proof.
  intros L Lad1 Lad2 H1 H2 w.
  pose (h := @rsminus R RIS SSx (Lad1 w) (Lad2 w)).
  assert (Hinner : req (rinner h h) zero).
  {
    unfold h.
    apply (req_trans _ _ _ (req_inner_sminus_r h (Lad1 w) (Lad2 w))).
    assert (Hmid : req (rinner h (Lad1 w)) (rinner h (Lad2 w)))
      by exact (req_trans _ _ _ (req_sym _ _ (H1 h w)) (H2 h w)).
    unfold req_minus.
    exact (req_trans _ _ _
      (req_plus_compat (rinner h (Lad1 w)) (rinner h (Lad1 w))
                       (opp (rinner h (Lad2 w))) (opp (rinner h (Lad1 w)))
                       (req_refl (rinner h (Lad1 w)))
                       (req_opp_compat (rinner h (Lad2 w)) (rinner h (Lad1 w))
                                       (req_sym _ _ Hmid)))
      (plus_opp (rinner h (Lad1 w)))).
  }
  assert (Hhzero : Id h rszero) by exact (rinner_definite h Hinner).
  unfold h in Hhzero.
  exact (req_sminus_zero_cancel (Lad1 w) (Lad2 w) Hhzero).
Qed.

(* Id op_lipschitz_compose L27409：|L∘M h| ≤ (N_L·N_M)·|h|
   （le_mult_compat_weak/mult_zero 接口字段链；加位判读经读证收敛：
   Id 证明零 plain 乘积非负依存，零新增假设位） *)
Lemma req_op_lipschitz_compose : forall (L M : @rSS R RIS SSx -> @rSS R RIS SSx),
  sigT (fun N : R => And (le zero N) (forall h : @rSS R RIS SSx,
    le (rsmetric (L (M h)) rszero) (mult N (rsmetric h rszero)))).
Proof.
  intros L M.
  destruct (rop_lipschitz L) as [NL [HNL0 HNL]].
  destruct (rop_lipschitz M) as [NM [HNM0 HNM]].
  exists (mult NL NM).
  split.
  - (* 0 ≤ NL·NM：mult_zero 换形 + le_mult_compat_weak *)
    apply (le_id_l _ (mult zero NM) _).
    + exact (req_trans _ _ _ (req_sym _ _ (mult_zero NM)) (mult_comm NM zero)).
    + exact (le_mult_compat_weak zero NL NM HNM0 HNL0).
  - intros h.
    apply (le_trans _ (mult NL (rsmetric (M h) rszero)) _).
    + exact (HNL (M h)).
    + apply (le_trans _ (mult NL (mult NM (rsmetric h rszero))) _).
      * apply (le_id_l _ (mult (rsmetric (M h) rszero) NL) _).
        { exact (mult_comm NL (rsmetric (M h) rszero)). }
        { apply (le_id_r _ (mult (mult NM (rsmetric h rszero)) NL) _).
          - exact (mult_comm (mult NM (rsmetric h rszero)) NL).
          - exact (le_mult_compat_weak (rsmetric (M h) rszero)
                     (mult NM (rsmetric h rszero)) NL HNL0 (HNM h)). }
      * apply (le_id_l _ (mult (mult NL NM) (rsmetric h rszero)) _).
        { exact (mult_assoc NL NM (rsmetric h rszero)). }
        { exact (le_refl (mult (mult NL NM) (rsmetric h rszero))). }
Qed.

(* Id mv_vec_diff_decomp L27450：通用误差分解（Hcancel + Hre 两段，
   与 req_compose_diff_decomp 同构——Hre Y X 的 req_sym） *)
Lemma req_mv_vec_diff_decomp : forall (A B X Y : R),
  req (req_minus A (plus B X)) (plus (req_minus A (plus B Y)) (req_minus Y X)).
Proof.
  intros A B X Y.
  assert (Hcancel : forall Z : R, req (plus (opp (plus B Z)) Z) (opp B)).
  {
    intro Z.
    apply (req_trans _ (plus (plus (opp B) (opp Z)) Z) _).
    - apply (req_plus_compat (opp (plus B Z)) (plus (opp B) (opp Z)) Z Z
                             (req_opp_plus B Z) (req_refl Z)).
    - apply (req_trans _ (plus (opp B) (plus (opp Z) Z)) _).
      + apply (req_sym _ _ (plus_assoc (opp B) (opp Z) Z)).
      + apply (req_trans _ (plus (opp B) zero) _).
        * apply (req_plus_compat (opp B) (opp B) (plus (opp Z) Z) zero
                                 (req_refl (opp B))).
          exact (req_trans _ _ _ (plus_comm (opp Z) Z) (plus_opp Z)).
        * apply plus_zero.
  }
  assert (Hre : forall Z1 Z2 : R,
    req (plus (plus A (opp (plus B Z1))) (plus Z1 (opp Z2)))
        (plus A (opp (plus B Z2)))).
  {
    intros Z1 Z2.
    apply (req_trans _ (plus A (plus (plus (opp (plus B Z1)) Z1) (opp Z2))) _).
    - exact (req_trans _ _ _
              (req_sym _ _ (plus_assoc A (opp (plus B Z1)) (plus Z1 (opp Z2))))
              (req_plus_compat A A _ _
                (req_refl A) (plus_assoc (opp (plus B Z1)) Z1 (opp Z2)))).
    - apply (req_trans _ (plus A (plus (opp B) (opp Z2))) _).
      + apply (req_plus_compat A A _ _ (req_refl A)).
        exact (req_plus_compat _ _ _ _ (Hcancel Z1) (req_refl (opp Z2))).
      + apply (req_plus_compat A A _ _ (req_refl A)).
        exact (req_sym _ _ (req_opp_plus B Z2)).
  }
  unfold req_minus.
  exact (req_sym _ _ (Hre Y X)).
Qed.

End ReqMultivar.
