# 算子演化论（OET）Lean 4 形式化工程

本包对应发布版本 `oet-vols-01-v1.0.0`，收录范围为 卷01：规范空间与算子。版本 DOI：10.5281/zenodo.21457931。
它包含本次收录范围内的全部项目 Lean 源码，包括定义、命题及习题解答的形式化。

## 构建

安装 [elan](https://github.com/leanprover/elan) 后，在本 README 所在目录运行：

```sh
lake exe cache get
lake build
```

第一步下载 mathlib 的预编译缓存以缩短构建时间，也可以省略；第二步验证整个发布工程。
首次运行需要联网取得工具链和外部依赖。`lean-toolchain` 固定 Lean 版本，
`lake-manifest.json` 固定依赖修订；请保留这两份文件。包内不包含下载缓存或编译产物，
构建不需要 Math Workspace，也不依赖未公开的后续卷。

## 源码与验证范围

`formal_oet.lean` 是本次发布的总入口，`formal_oet/` 保存按卷和主题组织的源码。
正文的定义、结论和题解对应具名 Lean 声明；部分注释保留写作阶段的稳定锚点，
公开正文中不显示这些内部锚点。编译验证以实际编码的对象、假设和结论为准。
