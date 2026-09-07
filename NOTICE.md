ConstructiveWorld-Main — 构造世界模块化形式化库（基座 + 28 模块信任缓存）
Copyright 2026 王宝军、夏挽岚（通讯作者 xiawanlan33@163.com）、祖光照、周志农、高雪峰 & Contributors

==========================================================================
SOURCE CODE LICENSE
==========================================================================

The Rocq/Coq formalization sources (.v) under ConstructiveWorld_Live/ and
ConstructiveWorld_vo/, the compiled trust caches (.vo) under
ConstructiveWorld_vo/, the single-file release builds (releases/), and the
documentation (docs/) in this repository are licensed under the Apache
License, Version 2.0.
See LICENSE for the full license text.

==========================================================================
RUNTIME COMPONENTS — LICENSE STATUS
==========================================================================

Certain runtime components have a different copyright status. See below
for details.

==========================================================================
1. EXTRACTED EXECUTABLE CHECKERS (RLA PROTECTED) — NONE PUBLISHED YET
==========================================================================

Unlike the .vo trust caches under ConstructiveWorld_vo/ — which are
development dependencies and are freely usable under Apache 2.0 — the RLA
(Runtime License Agreement, CLA/RLA.md) protection track of this project
covers future OCaml executable checkers and runtime components extracted
from the project modules via Coq Extraction.

No such component has been published as of this NOTICE. Each component
will be registered in the table below upon its first release.

| Component | Source | Status |
|-----------|--------|--------|
| （暂无已发布组件） | Coq Extraction（模块 .v → .ml → 可执行检查器） | 首次提取发布时登记；届时按 CLA/RLA.md 对商业使用实施保护 |

The Apache 2.0 license covers the source code and the .vo trust caches
(research / learning / reference / development use); the RLA governs
commercial use (embedding in products, SaaS, production environments) of
future extracted executable runtime components.
Contact 168888@live.cn for inquiries.

==========================================================================
THIRD-PARTY DEPENDENCIES
==========================================================================

This product includes or links to the following third-party software,
each governed by its own license:

1. The Rocq/Coq Proof Assistant — LGPL 2.1 (stdlib)
   - https://rocq-prover.org/
   - Used as: the proof assistant compiling all .v sources
   - This project depends only on the Rocq/Coq standard library
     (no mathcomp, no Coquelicot).

==========================================================================
ADDITIONAL ATTRIBUTIONS
==========================================================================

Portions of this work build on:
- The Rocq/Coq proof assistant: https://rocq-prover.org/
