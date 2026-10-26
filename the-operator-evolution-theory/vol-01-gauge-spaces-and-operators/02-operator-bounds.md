
<a id="oet-5d30f7f93769bbd7"></a>

## 第 2 章 算子界

本章考察如何用输入分量的距离，估计算子作用后的输出分量距离。为此，引入 Lipschitz 上界矩阵与 co-Lipschitz 下界矩阵，并讨论这些界在限制评估域和有限复合下的基本性质。

从本章起，我们需要在推导中明确结论所依据的数据及其满足的条件。为便于表述，先对“证书”这一术语作如下约定，并在全书中沿用。

> **约定（证书）**：若一组显式数据满足某个已证明命题的全部前提，并由该命题推出相应结论，则称这组数据为该结论的**证书**。


<a id="oet-af85899693cc8750"></a>

### 2.1 矩阵界与有限复合

#### Lipschitz 上界矩阵

**定义（Lipschitz 矩阵）**：对 $\phi \in \mathcal{X}_{\mathrm{op}}$，称非负矩阵 $\mathbf{L}$（$L_{i \to j} \in \bar{\mathbb{R}}_+$）为 $\phi$ 的一个**合法 Lipschitz 矩阵**，若对所有 $x, y \in \mathrm{dom}(\phi)$ 和所有 $j \in I$：

$$
d_j(\phi(x), \phi(y)) \;\leq\; \sum_{i \in I} L_{i \to j} \cdot d_i(x, y)
$$

书写矩阵 $\mathbf L$ 时，以输出分量为行指标、输入分量为列指标。因此，$L_{i\to j}$ 位于第 $j$ 行、第 $i$ 列，即 $(\mathbf L)_{ji}=L_{i\to j}$。除另有说明外，后文以 $i\to j$ 标记条目的矩阵，均沿用上述行列约定。

例如，当 $I=\{1,2,3\}$ 时，矩阵按通常的行列形式写为

$$
\mathbf L=
\begin{pmatrix}
L_{1\to1} & L_{2\to1} & L_{3\to1} \\
L_{1\to2} & L_{2\to2} & L_{3\to2} \\
L_{1\to3} & L_{2\to3} & L_{3\to3}
\end{pmatrix}.
$$

其中，第一行汇集指向输出分量 $d_1$ 的系数，第一列汇集从输入分量 $d_1$ 出发的系数。例如，$L_{2\to1}$ 位于第一行、第二列。

> **约定（广义 Lip）**：Lip 矩阵条目取值于 $\bar{\mathbb{R}}_+$（与 [§ 1.1](<01-foundations.md#user-content-oet-b4babd684de7c112>) 一致），即允许 $L_{i \to j} = +\infty$。需要有限性时显式标注。求和中的 $\bar{\mathbb{R}}_+$ 算术遵循 [§ 1.1](<01-foundations.md#user-content-oet-b4babd684de7c112>) 约定（特别地 $+\infty \cdot 0 = 0$）。即若某条目 $L_{i \to j} = +\infty$ 但 $d_i(x, y) = 0$，则该项对右端求和的贡献为零；这只说明该输入分量在该项中不贡献 $d_j$-输出上界，不排除其他输入分量或其他求和项给出非零贡献。当 $L_{i \to j} = +\infty$ 且 $d_i(x, y) > 0$ 时，该项为 $+\infty$，不等式平凡成立。

记 $\phi$ 的全体合法 Lip 矩阵之集为 $\mathscr{L}(\phi)$。本章始终把 $\mathscr L(\phi)$ 作为证书族使用，不预设其中存在同时实现所有条目下确界的指定矩阵。


<a id="oet-c4369c63c86cbacf"></a>

> **注（单分量情形下的标量 Lip 界）**：当 $|I|=1$ 且 $I=\{i\}$ 时，Lip 矩阵条件退化为单个标量不等式
>
> $$
> d_i(\phi(x),\phi(y))\le L_{i\to i}d_i(x,y)\qquad(x,y\in\mathrm{dom}(\phi)).
> $$
>
> **证明**：定义中的求和指标集只有一个元素 $i$，矩阵仅含条目 $L_{i\to i}$，代入 [§ 2.1](<#user-content-oet-af85899693cc8750>) 的 Lip 矩阵不等式即得。$\square$

**定义（子集受限 Lip 矩阵）**：对子集 $U \subseteq \mathrm{dom}(\phi)$，如果在 $U$ 上对任意 $x, y \in U$ 均满足上述距离放缩不等式，则称 $\mathbf{L}$ 为 $\phi$ 在 $U$ 上的一个受限 Lip 矩阵，记其合法矩阵集为 $\mathscr{L}(\phi)\big|_U$。


<a id="oet-4ff5c58d71e1651f"></a>

**引理 2.1（受限 Lip 矩阵族的单调性）**：固定算子 $\phi\in\mathcal X_{\mathrm{op}}$。若 $U\subseteq V\subseteq\mathrm{dom}(\phi)$，则

$$
\mathscr L(\phi)\big|_V\subseteq\mathscr L(\phi)\big|_U.
$$

特别地，对任意 $U\subseteq\mathrm{dom}(\phi)$，有

$$
\mathscr L(\phi)\subseteq\mathscr L(\phi)\big|_U.
$$

**证明**：取任意 $\mathbf L\in\mathscr L(\phi)\big|_V$。对任意 $x,y\in U$，由 $U\subseteq V$ 得 $x,y\in V$，故 $\mathbf L$ 在该点对上满足所有输出分量的 Lip 不等式。因此 $\mathbf L\in\mathscr L(\phi)\big|_U$。取 $V=\mathrm{dom}(\phi)$ 即得后一包含关系。$\square$


<a id="oet-193cebcc1a7f9259"></a>

**命题 2.2（Lip 矩阵复合律）**：对于复合算子 $\phi_2 \circ \phi_1$，选定起始定义域的局部子集 $U_1 \subseteq \mathrm{dom}(\phi_2 \circ \phi_1)$，记像集 $U_2 = \phi_1(U_1)$（由复合定义直接保证 $U_2 \subseteq \mathrm{dom}(\phi_2)$）。若 $\mathbf{L}^{(1)} \in \mathscr{L}(\phi_1)\big|_{U_1}$ 且 $\mathbf{L}^{(2)} \in \mathscr{L}(\phi_2)\big|_{U_2}$，则 $\mathbf{L}^{(2)} \cdot \mathbf{L}^{(1)} \in \mathscr{L}(\phi_2 \circ \phi_1)\big|_{U_1}$。

**证明**：对任意 $x, y \in U_1$，复合映射不仅合法，且有像点

$$
\phi_1(x),\phi_1(y)\in U_2.
$$

固定 $j\in I$。

根据 $\mathbf{L}^{(2)} \in \mathscr{L}(\phi_2)\big|_{U_2}$，代入像点对 $(\phi_1(x), \phi_1(y))$：

$$
d_j((\phi_2 \circ \phi_1)(x),(\phi_2 \circ \phi_1)(y))
\leq
\sum_{k \in I} L^{(2)}_{k \to j}\,d_k(\phi_1(x),\phi_1(y)).
$$

由于 $\mathbf{L}^{(1)} \in \mathscr{L}(\phi_1)\big|_{U_1}$，对一切 $k \in I$ 均有

$$
d_k(\phi_1(x),\phi_1(y))
\leq
\sum_{i \in I} L^{(1)}_{i \to k}\,d_i(x,y).
$$

因 $L^{(2)}_{k \to j} \geq 0$，同乘 $L^{(2)}_{k \to j}$ 并对 $k \in I$ 求和，不等号方向不变（由 $0 \cdot (+\infty) = 0$ 约定保证代数一致性）：

$$
\leq
\sum_{k \in I} L^{(2)}_{k \to j}
\left(\sum_{i \in I} L^{(1)}_{i \to k}\,d_i(x,y)\right).
$$

利用 $\bar{\mathbb{R}}_+$ 对有限和的加法交换律与乘法分配律，交换求和次序：

$$
=
\sum_{i \in I}
\left(\sum_{k \in I} L^{(2)}_{k \to j}L^{(1)}_{i \to k}\right)d_i(x,y).
$$

内部加和即为代数矩阵乘法元素 $(\mathbf{L}^{(2)} \cdot \mathbf{L}^{(1)})_{i \to j}$ 的定义，故 $\mathbf{L}^{(2)} \cdot \mathbf{L}^{(1)} \in \mathscr{L}(\phi_2 \circ \phi_1)\big|_{U_1}$。$\square$

#### co-Lipschitz 下界矩阵

**定义（子集受限 co-Lipschitz 矩阵）**：对 $\phi \in \mathcal{X}_{\mathrm{op}}$ 与给定的非空子集 $U \subseteq \mathrm{dom}(\phi)$，称非负矩阵 $\mathbf{K}$（$K_{i \to j} \in \bar{\mathbb{R}}_+$）为 $\phi$ 在 $U$ 上的一个**合法受限 co-Lipschitz 矩阵**（后续可简称为 co-Lip 矩阵），若对所有 $x, y \in U$ 和所有 $j \in I$：

$$
d_j(\phi(x), \phi(y)) \;\geq\; \sum_{i \in I} K_{i \to j} \cdot d_i(x, y)
$$

记 $\phi$ 在 $U$ 上的全体合法 co-Lip 矩阵之集为 $\mathscr{K}(\phi)\big|_U$。凡出现 $\mathscr{K}(\phi)\big|_U$，均包含这里的非空性条件 $U\neq\emptyset$。本章把该集合视为下界证书族，不预设其中存在同时实现所有条目上确界的指定矩阵。


<a id="oet-893b1d33535f7245"></a>

**引理 2.3（受限 co-Lip 矩阵族的单调性）**：固定算子 $\phi\in\mathcal X_{\mathrm{op}}$。若 $\varnothing\ne U\subseteq V\subseteq\mathrm{dom}(\phi)$，则

$$
\mathscr K(\phi)\big|_V\subseteq\mathscr K(\phi)\big|_U.
$$

特别地，对任意非空子集 $U\subseteq\mathrm{dom}(\phi)$，有

$$
\mathscr K(\phi)\big|_{\mathrm{dom}(\phi)}\subseteq\mathscr K(\phi)\big|_U.
$$

**证明**：取任意 $\mathbf K\in\mathscr K(\phi)\big|_V$。对任意 $x,y\in U$，由 $U\subseteq V$ 得 $x,y\in V$，故 $\mathbf K$ 在该点对上满足所有输出分量的 co-Lip 不等式。又因 $U$ 非空，故 $\mathbf K\in\mathscr K(\phi)\big|_U$。取 $V=\mathrm{dom}(\phi)$ 即得后一包含关系。$\square$


<a id="oet-88784dcbfff0ea66"></a>

> **注（co-Lip 条目为零的充分条件）**：若存在 $x,y\in\mathrm{dom}(\phi)$ 使
>
> $$
> d_j(\phi(x),\phi(y))=0,\qquad d_i(x,y)>0,
> $$
>
> 则任一全域 co-Lip 矩阵 $\mathbf K\in\mathscr K(\phi)\big|_{\mathrm{dom}(\phi)}$ 必满足 $K_{i\to j}=0$。
>
> **证明**：把该点对代入 co-Lip 不等式，得到
>
> $$
> 0=d_j(\phi(x),\phi(y))\ge \sum_{k\in I}K_{k\to j}d_k(x,y)\ge K_{i\to j}d_i(x,y).
> $$
>
> 由于 $K_{i\to j}\ge0$ 且 $d_i(x,y)>0$，只能有 $K_{i\to j}=0$。$\square$
>
> 选择受限域 $U$ 可以排除这类迫使特定 co-Lip 条目为零的点对；是否存在非零下界，仍须在所选域上另行验证。



<a id="oet-0f256e6f1d38a612"></a>

**命题 2.4（co-Lip 矩阵复合律）**：对于复合算子 $\phi_2 \circ \phi_1$，选定起始定义域的局部子集 $U_1 \subseteq \mathrm{dom}(\phi_2 \circ \phi_1)$，记像集 $U_2 = \phi_1(U_1)$（由复合定义直接保证 $U_2 \subseteq \mathrm{dom}(\phi_2)$）。若 $\mathbf{K}^{(1)} \in \mathscr{K}(\phi_1)\big|_{U_1}$ 且 $\mathbf{K}^{(2)} \in \mathscr{K}(\phi_2)\big|_{U_2}$，则 $\mathbf{K}^{(2)} \cdot \mathbf{K}^{(1)} \in \mathscr{K}(\phi_2 \circ \phi_1)\big|_{U_1}$。

**证明**：任取 $x,y\in U_1$ 与 $j\in I$。因 $\phi_1(x),\phi_1(y)\in U_2$，依次应用 $\mathbf K^{(2)}$、$\mathbf K^{(1)}$ 的 co-Lip 不等式，得到

$$
\begin{aligned}
&d_j((\phi_2\circ\phi_1)(x),(\phi_2\circ\phi_1)(y))\\
&\quad\geq \sum_{k\in I}K^{(2)}_{k\to j}\,d_k(\phi_1(x),\phi_1(y))\\
&\quad\geq \sum_{k\in I}K^{(2)}_{k\to j}
  \left(\sum_{i\in I}K^{(1)}_{i\to k}\,d_i(x,y)\right)\\
&\quad=\sum_{i\in I}
  \left(\sum_{k\in I}K^{(2)}_{k\to j}K^{(1)}_{i\to k}\right)d_i(x,y)\\
&\quad=\sum_{i\in I}(\mathbf K^{(2)}\cdot\mathbf K^{(1)})_{i\to j}\,d_i(x,y).
\end{aligned}
$$

这里乘以非负系数保持不等号方向；在 $0\cdot(+\infty)=0$ 的约定下，$\bar{\mathbb R}_+$ 的有限和可按分配律展开并交换次序。最后一行正是所需的 co-Lip 矩阵不等式。$\square$



#### 有限复合与矩阵乘积

将两步复合的矩阵界逐次应用，可得到有限复合的相应结论。


<a id="oet-c80171fa685dc795"></a>

**推论 2.5（有限复合的局部矩阵界）**：设有限复合 $c_k=\phi_k\circ\cdots\circ\phi_1$（$k\geq1$），并取起始定义域子集 $U_1 \subseteq \mathrm{dom}(c_k)$。递归定义中间像集 $U_{m+1} = \phi_m(U_m)$（$m = 1, \dots, k$）。在复合链语境中，若无特别说明，$\mathbf L^{(m)}$、$\mathbf K^{(m)}$ 分别表示第 $m$ 步在实际输入域 $U_m$ 上选取的局部证书。则全复合具有以下局部矩阵界：

**(i) Lip 上界**：若各单步具有合法矩阵 $\mathbf{L}^{(m)} \in \mathscr{L}(\phi_m)\big|_{U_m}$，则全复合满足：
$$
\mathbf{L}^{(k)} \cdot \cdots \cdot \mathbf{L}^{(1)} \;\in\; \mathscr{L}(c_k)\big|_{U_1}
$$

**(ii) co-Lip 下界**：若各单步具有合法矩阵 $\mathbf{K}^{(m)} \in \mathscr{K}(\phi_m)\big|_{U_m}$，则全复合满足：
$$
\mathbf{K}^{(k)} \cdot \cdots \cdot \mathbf{K}^{(1)} \;\in\; \mathscr{K}(c_k)\big|_{U_1}
$$

**证明**：由 $U_1 \subseteq \mathrm{dom}(c_k)$ 与复合定义逐步递推，得

$$
U_m \subseteq \mathrm{dom}(\phi_m)
\qquad(m=1,\ldots,k).
$$

分别对 [命题 2.2](<#user-content-oet-193cebcc1a7f9259>) 与 [命题 2.4](<#user-content-oet-0f256e6f1d38a612>) 做有限归纳，即得 (i) 与 (ii)。$\square$


<a id="oet-11006ddd8c43bfec"></a>

> **注（零步复合的单位矩阵证书）**：当边界情形 $k=0$ 时，$c_0 = \mathrm{id}_{\mathcal{X}}$。定义矩阵空复合乘积为单位矩阵 $\mathbf{I}$。对任意非空 $U \subseteq \mathrm{dom}(\mathrm{id}_{\mathcal{X}})$，$\mathbf{I} \in \mathscr{L}(\mathrm{id}_{\mathcal{X}})\big|_U \cap \mathscr{K}(\mathrm{id}_{\mathcal{X}})\big|_U$。
>
> **证明**：恒等映射满足 $d_j(x,y)=\sum_{i\in I}\mathbf{I}_{i\to j}d_i(x,y)$，故同一单位矩阵同时满足 Lip 与 co-Lip 不等式。$\square$

该推论只断言所选单步证书的连乘仍是合法证书，不断言所得矩阵在全复合的证书族中具有任何极值性质。


<a id="oet-e4154c34e95d3c23"></a>

**命题 2.6（有限矩阵乘积条目的零值与正值判据）**：设 $\mathbf M^{(1)},\ldots,\mathbf M^{(n)}$ 为以 $I$ 为指标集的扩展非负矩阵，$n\ge1$。则对任意 $i,j\in I$：

**(i)（零值判据）**：$[\mathbf{M}^{(n)}\cdots\mathbf{M}^{(1)}]_{i \to j}=0$，当且仅当对任意指标序列 $(k_1, k_2, \dots, k_{n-1})$，必然存在至少一个层级 $m \in \{1,\dots,n\}$ 使得：
$$
 [\mathbf{M}^{(m)}]_{k_{m-1} \to k_m} = 0
$$
（其中约定起止指标 $k_0 = i, k_n = j$）。

**(ii)（正值判据）**：$[\mathbf{M}^{(n)}\cdots\mathbf{M}^{(1)}]_{i \to j}>0$，当且仅当存在**至少一条**指标序列 $(k_1, k_2, \dots, k_{n-1})$，使得沿该路径的所有单步矩阵条目均严格正：
$$
 \forall m \in \{1,\dots,n\},\quad [\mathbf{M}^{(m)}]_{k_{m-1} \to k_m} > 0
$$

当 $n=1$ 时，中间指标序列为空，唯一空序列按约定满足 $k_0=i$、$k_1=j$；上述两条判据分别退化为单个矩阵条目 $[\mathbf{M}^{(1)}]_{i\to j}=0$ 与 $[\mathbf{M}^{(1)}]_{i\to j}>0$。

**证明**：将矩阵乘积按定义在 $\bar{\mathbb{R}}_+$ 中展开：
当 $n=1$ 时展开式就是 $[\mathbf{M}^{(1)}]_{i\to j}$；当 $n\ge2$ 时，

$$
[\mathbf{M}^{(n)} \cdots \mathbf{M}^{(1)}]_{i \to j} = \sum_{k_{n-1}\in I} \cdots \sum_{k_1\in I} \left( [\mathbf{M}^{(n)}]_{k_{n-1} \to j} \cdots [\mathbf{M}^{(2)}]_{k_1 \to k_2} \cdot [\mathbf{M}^{(1)}]_{i \to k_1} \right).
$$

**(i)** 由于 $\bar{\mathbb{R}}_+$ 中所有求和项皆非负，多项总和为 $0$ 的充要条件是每一条路径乘积严格等于 $0$。由乘法规则（含 $0 \cdot +\infty = 0$ 约定），乘积为 $0$ 等价于其因子中存在至少一个零元素。

**(ii)** 若矩阵乘积条目严格为正，则路径展开中至少有一项严格为正，故该路径上所有因子均严格为正。反之，若存在一条所有因子均严格为正的路径，则其乘积严格为正；全部路径乘积之和不小于该项，故矩阵乘积条目严格为正。$\square$

对已选取的 Lip 或 co-Lip 证书序列，令 $\mathbf M^{(m)}=\mathbf L^{(m)}$ 或 $\mathbf M^{(m)}=\mathbf K^{(m)}$，即可分别判断其乘积条目何时为零或严格为正。

#### 算子扰动

复合估计固定了各步算子。若改动算子本身，受限算子距离还给出以下像点距离的扰动估计。


<a id="oet-b959b42f25710105"></a>

**命题 2.7（算子扰动下的像点距离界）**：设 $\phi_1,\phi_2\in\mathcal X_{\mathrm{op}}$，$U\subseteq\mathrm{dom}(\phi_1,\phi_2)$。若存在 $\boldsymbol\varepsilon=(\varepsilon_j)_{j\in I}\in\bar{\mathbb R}_+^I$，使得对任意 $z\in U$ 与 $j\in I$，

$$
d_j(\phi_1(z),\phi_2(z))\le \varepsilon_j,
$$

则对任意 $x,y\in U$ 与 $j\in I$：

**(i)（点对像距双向扰动）**

$$
d_j(\phi_2(x),\phi_2(y))
\le
d_j(\phi_1(x),\phi_1(y))+2\varepsilon_j,
$$

且交换 $\phi_1,\phi_2$ 得

$$
d_j(\phi_1(x),\phi_1(y))
\le
d_j(\phi_2(x),\phi_2(y))+2\varepsilon_j.
$$

**(ii)（Lip 上界的扰动估计）** 若 $\mathbf L_1\in\mathscr L(\phi_1)\big|_U$，则

$$
d_j(\phi_2(x),\phi_2(y))
\le
\sum_{i\in I}[\mathbf L_1]_{i\to j}d_i(x,y)+2\varepsilon_j.
$$

**(iii)（co-Lip 下界的扰动估计）** 若 $\mathbf K_1\in\mathscr K(\phi_1)\big|_U$，则

$$
\sum_{i\in I}[\mathbf K_1]_{i\to j}d_i(x,y)
\le
d_j(\phi_2(x),\phi_2(y))+2\varepsilon_j.
$$

交换 $\phi_1,\phi_2$ 后，可得到 $\phi_2$ 的 Lip 或 co-Lip 证书对 $\phi_1$ 的对应扰动估计。

**证明**：由伪度量对称性，扰动前提也给出

$$
d_j(\phi_2(z),\phi_1(z))\le \varepsilon_j
\qquad(z\in U,\ j\in I).
$$

对 $x,y\in U$，三角不等式给出

$$
d_j(\phi_2(x),\phi_2(y))
\le
d_j(\phi_2(x),\phi_1(x))
+d_j(\phi_1(x),\phi_1(y))
+d_j(\phi_1(y),\phi_2(y)).
$$

首尾两项均由扰动前提控制，故得到 (i) 的第一式；交换 $\phi_1,\phi_2$ 得第二式。

若 $\mathbf L_1\in\mathscr L(\phi_1)\big|_U$，则

$$
d_j(\phi_1(x),\phi_1(y))
\le
\sum_{i\in I}[\mathbf L_1]_{i\to j}d_i(x,y).
$$

代入 (i) 的第一式即得 (ii)。若 $\mathbf K_1\in\mathscr K(\phi_1)\big|_U$，则

$$
\sum_{i\in I}[\mathbf K_1]_{i\to j}d_i(x,y)
\le
d_j(\phi_1(x),\phi_1(y)).
$$

再由 (i) 的第二式放缩，即得 (iii)。$\square$


<a id="oet-7fa97eb6e24d5527"></a>

### 2.2 分量通道

**定义（分量通道）**：对 $i,j\in I$，称有序对 $(i,j)$ 为从输入分量 $d_i$ 到输出分量 $d_j$ 的一个**分量通道**。

设 $\phi\in\mathcal X_{\mathrm{op}}$，$U\subseteq\mathrm{dom}(\phi)$，并选取受限 Lip 证书 $\mathbf L\in\mathscr L(\phi)\big|_U$。条目 $L_{i\to j}$ 是输入分量 $d_i$ 在输出分量 $d_j$ 上界中的系数；若其为零，相应项便不参与该上界。

特别地，若第 $j$ 行除 $L_{i\to j}$ 外均为零，则对任意 $x,y\in U$，Lip 不等式化为

$$
d_j(\phi(x),\phi(y))
\le \sum_{k\in I}L_{k\to j}d_k(x,y)
=L_{i\to j}d_i(x,y).
$$

若 $\mathbf L$ 为对角矩阵，上述化简对每个同分量通道 $(i,i)$ 均成立。


<a id="oet-f82672ec0dd48f28"></a>

**命题 2.8（正 co-Lip 通道保持可分辨性）**：设 $\mathbf K\in\mathscr K(\phi)\big|_U$。

**(i)** 若 $K_{i\to j}>0$，则对任意 $x,y\in U$，

$$
d_i(x,y)>0
\quad\Longrightarrow\quad
d_j(\phi(x),\phi(y))>0.
$$

**(ii)** 若 $K_{j\to j}>0$ 对所有 $j\in I$ 成立，则 $\phi$ 反射族零距关系：对任意 $x,y\in U$，

$$
\phi(x)\sim_{\mathcal G}\phi(y)
\quad\Longrightarrow\quad
x\sim_{\mathcal G}y.
$$

**证明**：对任意 $x,y\in U$，co-Lip 不等式与非负性给出

$$
d_j(\phi(x),\phi(y))
\ge
\sum_{k\in I}K_{k\to j}d_k(x,y)
\ge
K_{i\to j}d_i(x,y).
$$

若 $K_{i\to j}>0$ 且 $d_i(x,y)>0$，则右侧严格大于零，故 (i) 成立。

对 (ii)，设 $\phi(x)\sim_{\mathcal G}\phi(y)$。固定 $j\in I$；若 $d_j(x,y)>0$，则由 (i) 取通道 $(j,j)$ 可得 $d_j(\phi(x),\phi(y))>0$，与族零距关系矛盾。因此 $d_j(x,y)=0$。由于 $j$ 任意，得到 $x\sim_{\mathcal G}y$。$\square$

本章用 Lip 矩阵与 co-Lip 矩阵描述算子的分量距离界，并讨论这些界在限制评估域和算子复合下的基本性质。接下来，我们考察分量距离在算子作用后归零的情形，进一步讨论算子的局部退化。


<a id="oet-24393c02126250b8"></a>

### 2.3 习题


<div data-mb-exercise="oet-b2cea3f1af318f29">

**习题 2.1（同一算子的两组规范）**：设 $\mathcal X=\mathbb R^2\sqcup\{\bot\}$，算子 $\phi$ 由

$$
\phi(s,t)=(s,s+t),\qquad \phi(\bot)=\bot
$$

给出。以下伪度量均按吸收元约定延拓，Lip 界均在 $\mathbb R^2$ 上考察。

**(i)** 取

$$
d_1(x,y)=|x_1-y_1|,\qquad
d_2(x,y)=|x_1-y_1|+|x_2-y_2|.
$$

验证 $\phi$ 具有对角 Lip 证书

$$
\mathbf L=\begin{pmatrix}1&0\\0&2\end{pmatrix}.
$$

**(ii)** 保持 $\phi$ 与 $d_1$ 不变，将 $d_2$ 替换为

$$
\widetilde d_2(x,y)=|x_2-y_2|.
$$

给出这组规范下的一个 Lip 证书，并证明任意 Lip 证书 $\mathbf M$ 均满足 $M_{1\to2}\ge1$。

</div>



<div data-mb-exercise="oet-6a98a58b5bc95360">

**习题 2.2（对角输入项的标量双侧界）**：设 $\phi \in \mathcal{X}_{\mathrm{op}}$，$U \subseteq \mathrm{dom}(\phi)$，$j \in I$。给定 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 与 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$。若 $\phi$ 在 $U$ 上关于输出分量 $d_j$ 满足只保留对角输入项的 Lip 上界

$$
L_{k \to j} = 0\quad(\forall k \neq j),
$$

证明对任意 $x,y\in U$ 有标量双侧不等式：

$$
K_{j \to j} \cdot d_j(x, y) \;\leq\; d_j(\phi(x), \phi(y)) \;\leq\; L_{j \to j} \cdot d_j(x, y)
$$

</div>
