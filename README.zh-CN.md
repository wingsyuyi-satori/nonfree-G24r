# 分子 24 的统一非自由性：Lean 形式化

作者：Ziheng Wang  
单位：University of Chinese Academy of Sciences, Hangzhou Institute for Advanced Study, Hangzhou, China  
AI assistance: GPT-6-Astra.

公开仓库：[wingsyuyi-satori/nonfree-G24r](https://github.com/wingsyuyi-satori/nonfree-G24r)。
版本：**0.1.0**。论文与 Lean 项目将一起作为软件记录归档至 Zenodo，取得 DOI 后更新引用信息。

这是一个固定 Lean 4.24.0 / mathlib v4.24.0 的可重建项目。证明对象为有理矩阵

$$
 A=\begin{pmatrix}1&0\\1&1\end{pmatrix},\qquad
 B_q=\begin{pmatrix}1&q\\0&1\end{pmatrix},\qquad
 G_q=\langle A,B_q\rangle\leq\mathrm{SL}_2(\mathbb Q).
$$

## 主结论

对每个整数 $r$，若 $|r|>6$，则 $G_{24/r}$ 不是抽象自由群。

- `twentyfour_not_free : Challenge.MainStatement`：完整的 `¬ IsFreeGroup` 结论。
- `twentyfour_hasRelation : Challenge.RelationStatement`：确实存在二生成元自由群中的非单位元，其矩阵像是单位元。
- `twentyfour_twoStep : Challenge.TwoStepStatement`：当 `|r| > 17` 时，存在以 B 开始并结束、指数全非零的 1/3/5 音节三角词。
- `twentyfour_boundedRelation : Challenge.BoundedStatement`：每个这样的分母都有非空、约化、非平凡的关系词，最多 64 个交替非零幂音节。此上界不是展开指数后的普通字母数上界。

项目还形式化了有理矩阵到 `SL(2, ℂ)` 的逐项单射、两个生成子群的同构，以及真实复矩阵版本的非自由性。`twentyfour_complex_not_free : Challenge.ComplexMainStatement` 是相应独立目标的证明。

## 证明结构

- `Core.lean`：矩阵、真实自由群、非平凡约化词、三角化与显式关系词。
- `SimpleDirect.lean`：固定参数、无分支的五块恒等式及 12 音节关系族。
- `ParametricArithmetic.lean` / `Parametric.lean`：一般五块参数构造及早期直接族的补充证明。
- `GoodRuleArithmetic.lean` / `GoodRule.lean`：一般覆盖规则的规范化和关系词构造。
- `FiniteCover.lean`：48 条规则和模 40320 的完整有限覆盖证书，剩余 4 类。
- `FiniteWords.lean`：23 个例外绝对分母的精确关系词证书。
- `CoverBridge.lean` / `CoverRelations.lean` / `Main.lean`：从有限证书到所有整数分母的证明。
- `ComplexVersion.lean`：有理与复数矩阵生成群的同构，以及 `SL(2, ℂ)` 中的结论。
- `FreeGroupHopf.lean` / `NonFree.lean`：有限模型分离、有限生成自由群的 Hopf 性，以及从非平凡关系到抽象非自由性的完整桥梁。
- `Bounded.lean`：保持约化性、非平凡性和音节数上界的统一关系词证明。
- `TwoStep.lean`：显式余有限 two-step 推论及三角词的非平凡性。

有限计算使用内核可复核的 `decide`。项目不使用 `sorry`、自定义公理、`native_decide` 或编译器 oracle 作为证明占位。

## 独立命题与证明

参考 [anthropics/formal-math](https://github.com/anthropics/formal-math) 的分层方式：

- `Challenge.lean` 只导入 Mathlib，独立写出矩阵、生成子群和目标命题。
- `Solution.lean` 提供目标命题的证明；与实现中定义的一致性由 Lean 检查。
- `AxiomAudit.lean` 检查最终声明及关键中间定理的完整公理依赖。

独立 Challenge 以命题定义写出目标，Solution 给出实际证明。原研究包记录了 Lean 内核检查、完整公理审计与直接 nanoda 重放，后者检查了 18,169 个声明且无错误。本次仓库整理核对了全部 19 个 Lean 源文件与原验证哈希的一致性，并重新运行精确有限计算；整理所用的机器未重新构建 Lean 或重放 nanoda。

完整 comparator/Palomar 验收在原验证环境中未完成：其固定版本的 checker 预期 Lean 4.24 中不存在的 `String.ofList`，原环境也不支持所需 Landlock 沙箱。未修改 checker 或绕过沙箱，具体版本与验证范围见 `VERIFICATION.md`。

## 仓库检查

使用 Python **3.9 或更新版本**即可运行发布检查：

```sh
python3 scripts/check-release.py
```

检查包括 Lean 验证源文件哈希、论文文件哈希、引用与归档元数据、完整发布清单，以及模 40320 的全部剩余类和 23 个例外词。重新生成的数据表与报告必须和提交版本逐字节一致。

`python3 scripts/make-delivery.py` 生成发布 ZIP 和 SHA-256 校验文件。修改 Lean 证明源文件后，需要先更新实际验证证据，才能打包。

## 复现

安装 [Lean 官方 elan](https://github.com/leanprover/elan)，并确保 `git`、Python 3 和 Bash 可用。进入项目目录：

```sh
lake exe cache get
lake build Solution
bash scripts/verify.sh twentyfour_not_free twentyfour_hasRelation twentyfour_boundedRelation twentyfour_complex_not_free twentyfour_twoStep
```

第二个独立内核检查器需要 [Rust/cargo](https://rust-lang.org/tools/install/)：

```sh
bash scripts/bootstrap-checkers.sh
bash scripts/verify-nanoda.sh Solution twentyfour_not_free twentyfour_hasRelation twentyfour_boundedRelation twentyfour_complex_not_free twentyfour_twoStep
```

最终实际检查的完整定理名单位于 `logs/nanoda-theorems.txt`；可将其所有名字传给两个验证脚本。首次下载缓存及构建有限证书需要数分钟。

精确版本见 `lean-toolchain`、`lake-manifest.json` 和 `verification-pins.json`。各层验证的状态和范围见 `verification-result.json` 与 `VERIFICATION.md`，原始文本日志位于 `logs/`。交付包不含下载的工具、Mathlib、缓存、参考仓库或原始研究文本；文件完整性清单位于 `package-manifest.json`。

软件与 Lean 代码采用 MIT（`LICENSE`）；论文及 `paper/` 中的稿件采用 CC BY 4.0（`LICENSE-PAPER.md`）。引用与软件归档信息见 `CITATION.cff`、`.zenodo.json`，已填入正式仓库地址。DOI 待 Zenodo 分配后补入；未填写邮箱或 ORCID。
