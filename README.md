# 算子演化论（OET）

**当前发布：第一卷《规范空间与算子》 · v1.0.0 · 中文**

- **在线阅读**：[第一卷网页版](https://glenzli.com/books/oet/)（目录、公式、插图与习题解答跳转）
- **PDF 阅读与下载**：[在线阅读（GitLab）](https://gitlab.com/glenzli/oet-public/-/releases/oet-vols-01-v1.0.0/downloads/oet-vols-01-v1.0.0-publication.pdf) · [GitHub 下载](https://github.com/glenzli/oet-public/releases/download/oet-vols-01-v1.0.0/oet-vols-01-v1.0.0-publication.pdf) · [Zenodo 下载](https://zenodo.org/records/21457931/files/oet-vols-01-v1.0.0-publication.pdf)
- **第一卷完整 Lean 工程**：[GitHub 下载](https://github.com/glenzli/oet-public/releases/download/oet-vols-01-v1.0.0/oet-vols-01-v1.0.0-lean-prefix-source.tar.gz) · [GitLab 下载](https://gitlab.com/glenzli/oet-public/-/releases/oet-vols-01-v1.0.0/downloads/oet-vols-01-v1.0.0-lean-prefix-source.tar.gz) · [构建说明](the-operator-evolution-theory/formal-oet/README.md)
- **Zenodo 本版存档与引用**：[10.5281/zenodo.21457931](https://doi.org/10.5281/zenodo.21457931) · [引用格式](CITATION.zh-CN.md)

<!-- OET-CONCEPT-DOI:START -->
系列 DOI：[10.5281/zenodo.21457930](https://doi.org/10.5281/zenodo.21457930)，代表全部版本，并指向最新发布版。引用本次第一卷时，请使用上方的版本 DOI。
<!-- OET-CONCEPT-DOI:END -->

## 关于这份书稿

算子演化论（Operator Evolution Theory，OET）最初的想法来自对计算过程的观察：不同输入可能对应不同的小函数复合链路，能否按输入区域分别研究它们？随着写作和整理，讨论逐渐转向一般的空间与算子，用一族伪度量保留不同方面的比较，考察这些差异在变换中如何被放大、缩小或消去，以及多个变换接续作用时的整体表现。

第一卷从这些问题出发，建立规范空间与算子的基本语言，进而讨论算子链和有限算子网络。书稿仍在持续编写和审核，后续关于拟合与演化的内容会继续整理和验证。本次发布包括第一卷的中文正文、习题与解答，以及对应的 Lean 4 形式化工程，暂不提供翻译版。研究过程可见[写在前面](the-operator-evolution-theory/front-matter/00-preface.md)，后续计划可见[未完待续](the-operator-evolution-theory/to-be-continued.md)。

## 源码与验证

- [正文 Markdown](the-operator-evolution-theory/)：便于检索与查看源码；连续阅读可使用上方网页版或 PDF。
- [Lean 4 工程](the-operator-evolution-theory/formal-oet/)：包含本次发布范围内的项目源码、工具链与依赖锁定文件和构建说明。首次构建需要联网取得工具链与外部依赖，不需要 Math Workspace 或未公开的后续卷。

网页版及当前仓库补齐了第一卷的四张插图，并恢复了正文引用与习题解答跳转。v1.0.0 原始源码压缩包遗漏了这四张图，已封存的 PDF 中图片完整；原始发布文件与标签保持不变，详见[阅读包说明](release/README.md#web-reading-companion)。

本版公开 Lean 工程已完整构建通过。协作与审阅方式见 [AI 参与及责任说明](AI-PARTICIPATION-SUMMARY.md)。

## 版本、许可与项目入口

本次发布标签为 `oet-vols-01-v1.0.0`。PDF 与源码包保存在 [GitHub Release](https://github.com/glenzli/oet-public/releases/tag/oet-vols-01-v1.0.0)、[GitLab Release](https://gitlab.com/glenzli/oet-public/-/releases/oet-vols-01-v1.0.0) 和 Zenodo，发布文件附有签名清单与校验和。

本作品采用 [CC BY 4.0 许可](LICENSE.zh-CN.md)。引用方式见[引用说明](CITATION.zh-CN.md)，AI 使用中的署名说明见 [AI 署名声明](AI_ATTRIBUTION_NOTICE.zh-CN.md)。

[作品主页](https://glenzli.com/books/oet/) · [GitHub 仓库](https://github.com/glenzli/oet-public) · [GitLab 仓库](https://gitlab.com/glenzli/oet-public)
