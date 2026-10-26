## 第 1 章 基础

本章先用有限族分量伪度量描述集合上的不同分辨关系，再用覆盖数与度量熵衡量有限精度下的分辨量，最后把点之间的距离提升到算子之间。由此建立后续比较算子作用及其复合所需的空间与记号。

### 1.1 扩展规范空间

**定义（扩展规范空间）**：设 $\mathcal{X}$ 为集合，$\bot \in \mathcal{X}$ 为指定的**吸收元**，并要求非吸收部分非空：

$$
\mathcal{X}\setminus\{\bot\}\neq\emptyset.
$$

$\mathcal{X}$ 上的一个**规范结构** $\mathcal{G} = \{d_i\}_{i \in I}$（$I$ 为有限非空指标集）是一族**扩展伪度量**，每个 $d_i: \mathcal{X} \times \mathcal{X} \to \bar{\mathbb{R}}_+ = [0, +\infty]$ 满足：

**(i)** $d_i(x, x) = 0$，

**(ii)** $d_i(x, y) = d_i(y, x)$（对称），

**(iii)** $d_i(x, z) \leq d_i(x, y) + d_i(y, z)$（三角不等式），

**(iv)** $d_i(x, \bot) = +\infty$（$\forall\, x \neq \bot$，吸收元隔离）。

> **约定（$\bar{\mathbb{R}}_+$ 算术）**：全文采用标准扩展非负实数算术：$a + (+\infty) = +\infty$，$0 \cdot (+\infty) = 0$，$a \cdot (+\infty) = +\infty$（$a > 0$）。

称三元组 $(\mathcal{X}, \mathcal{G}, \bot)$ 为**扩展规范空间**（简称**规范空间**）。公理 (iv) 使 $\bot$ 在度量上与 $\mathcal{X} \setminus \{\bot\}$ 完全隔离；$\bot$ 的代数功能见 § 1.3。每个 $d_i$ 称为 $\mathcal{G}$ 的一个**分量（扩展）伪度量**，后续简称**分量伪度量**。

另外，对 $\mathcal X$ 的子集作如下约定。

> **约定（子集排除吸收元）**：后文选取 $\mathcal{X}$ 的子集时，除非另有说明，均默认不含 $\bot$；由公式明确给出的集合按其定义理解。

对 $x_0 \in \mathcal{X}$、$r \in (0, +\infty)$ 与分量伪度量 $d_i$，定义**开球**：

$$B_i(x_0, r) := \{x \in \mathcal{X} : d_i(x, x_0) < r\}$$

> **约定（半径的值域）**：本书中，开球半径 $r$ 取有限正实数（$0 < r < +\infty$）。若后文对一族有限正半径取上确界，该上确界本身允许等于 $+\infty$；但这不把 $B_i(x_0,+\infty)$ 变成合法开球。

**定义（族零距关系与族分离性）**：对任意 $x,y\in\mathcal X$，定义

$$
x\sim_{\mathcal G}y
\quad\Longleftrightarrow\quad
d_i(x,y)=0\qquad(\forall i\in I).
$$

若

$$
x\sim_{\mathcal G}y\quad\Longrightarrow\quad x=y
$$

对所有 $x,y\in\mathcal X$ 成立，则称规范族 $\mathcal G$ **分离** $\mathcal X$，并称相应规范空间为**分离规范空间**；否则称其为**非分离规范空间**。

**引理 1.1（族零距关系是等价关系）**：$\sim_{\mathcal G}$ 是 $\mathcal X$ 上的等价关系。

**证明**：自反性由 $d_i(x,x)=0$ 得到；对称性由每个 $d_i$ 的对称性得到。若 $x\sim_{\mathcal G}y$ 且 $y\sim_{\mathcal G}z$，则对任意 $i\in I$，

$$
0\le d_i(x,z)\le d_i(x,y)+d_i(y,z)=0,
$$

故 $d_i(x,z)=0$，即 $x\sim_{\mathcal G}z$。$\square$

> **约定（正文不预设族分离性）**：除非另有说明，本卷不预设族分离性；全分量零距离不必意味着两点相同。

### 1.2 空间覆盖与度量熵

固定分辨精度后，考察集合能否被有限个以内部点为中心的开球覆盖。若能，所需中心的最少数量给出这一精度下的分辨量。

**定义（覆盖数）**：对分量伪度量 $d_i$、精度 $\varepsilon \in (0, +\infty)$ 与子集 $U \subseteq \mathcal{X}$，定义 $U$ 在 $d_i$ 下的 $\varepsilon$-**覆盖数**：

$$\mathcal{N}_i(\varepsilon, U) := \min\bigl\{|S| : S \subseteq U,\; |S| < \infty,\; U \subseteq \textstyle\bigcup_{s \in S} B_i(s, \varepsilon)\bigr\}$$

即从 $U$ 内部选取中心点、以开球覆盖 $U$ 所需的最小点数（内覆盖）。若 $U$ 不可有限覆盖则 $\mathcal{N}_i(\varepsilon, U) = +\infty$；由定义，$\mathcal{N}_i(\varepsilon, \emptyset) = 0$。

对任意非空指标子族 $J\subseteq I$，定义**子族复合伪度量**

$$d_J(x,y):=\max_{j\in J}d_j(x,y).$$

由于 $I$ 有限，$d_J$ 仍为扩展伪度量。对 $x_0\in\mathcal X$ 与 $r\in(0,+\infty)$，定义其对应的开球：

$$
B_J(x_0,r):=\{x\in\mathcal X:d_J(x,x_0)<r\}.
$$

对 $S\subseteq\mathcal X$，以 $B_J$ 代替 $B_i$，按上述覆盖数定义得到的量记为 $\mathcal N_J(\varepsilon,S)$，称为 $S$ 在 $d_J$ 下的 $\varepsilon$-**子族覆盖数**，并沿用上述约定。当 $J=\{i\}$ 时，$\mathcal N_J(\varepsilon,S)=\mathcal N_i(\varepsilon,S)$。

**定义（度量熵）**：基于覆盖数定义单分量度量熵：

$$E_{\varepsilon, i}(U) := \log_2 \mathcal{N}_i\bigl(\varepsilon,\, U\bigr)$$

并基于子族覆盖数定义**子族度量熵**

$$
E_{\varepsilon,J}(S):=\log_2\mathcal N_J(\varepsilon,S).
$$

当 $J=\{i\}$ 时，$E_{\varepsilon,J}(S)=E_{\varepsilon,i}(S)$。$E_{\varepsilon, i}$ 与 $E_{\varepsilon,J}$ 对非空子集取值于 $\bar{\mathbb{R}}_+ = [0, +\infty]$；约定空集熵为 $\log_2 0 = -\infty$。

> **约定（对数底数）**：全文采用以 $2$ 为底的对数 $\log_2$。

### 1.3 算子空间与诱导规范

用吸收元统一表示未定义的输出后，可以在普通函数复合下讨论偏定义映射，并用各输入处的输出距离比较两个映射。

**定义（算子空间）**：

$$\mathcal{X}_{\mathrm{op}} = \{\, \phi : \mathcal{X} \to \mathcal{X} \;\big|\; \phi(\bot) = \bot \,\}$$

$\phi \in \mathcal{X}_{\mathrm{op}}$ 称为 $\mathcal{X}$ 上的一个**算子**。条件 $\phi(\bot) = \bot$ 保证吸收元在所有算子下不变；$\phi(x) = \bot$ 表示 $\phi$ 在 $x$ 处未定义。指定 $\mathcal{X}_{\mathrm{op}}$ 的**吸收元** $\bot_{\mathrm{op}} \in \mathcal{X}_{\mathrm{op}}$ 为全未定义算子：$\bot_{\mathrm{op}}(x) = \bot$（$\forall x \in \mathcal{X}$）。

定义其**定义域**：

$$\mathrm{dom}(\phi) := \bigl\{\, x \in \mathcal{X} \;\big|\; \phi(x) \neq \bot \,\bigr\}$$

> **约定（公共定义域简写）**：对有限族 $\phi_1,\ldots,\phi_n\in\mathcal{X}_{\mathrm{op}}$（$n\geq1$），记
>
> $$\mathrm{dom}(\phi_1,\ldots,\phi_n) := \bigcap_{r=1}^n\mathrm{dom}(\phi_r).$$
>
> 特别地，$\mathrm{dom}(\phi,\psi)=\mathrm{dom}(\phi)\cap\mathrm{dom}(\psi)$。

由 $\phi(\bot) = \bot$，对所有 $\phi \in \mathcal{X}_{\mathrm{op}}$ 均有 $\bot \notin \mathrm{dom}(\phi)$。定义其**像集**：

$$\mathrm{Im}(\phi) := \phi(\mathrm{dom}(\phi)) = \{\phi(x) : x \in \mathrm{dom}(\phi)\}$$

由定义域排除 $\bot$ 及 $x \in \mathrm{dom}(\phi) \Rightarrow \phi(x) \neq \bot$，故 $\bot \notin \mathrm{Im}(\phi)$。$\bot$ 的作用是将偏函数统一为全函数，$\mathrm{dom}(\phi)$ 与 $\mathrm{Im}(\phi)$ 分别刻画 $\phi$ 给出有意义输出的源点与目标点区域。$\mathcal{X}_{\mathrm{op}}$ 在函数复合下构成**幺半群**：封闭性 $\phi_2 \circ \phi_1 \in \mathcal{X}_{\mathrm{op}}$（由 $(\phi_2 \circ \phi_1)(\bot) = \phi_2(\bot) = \bot$），单位元 $\mathrm{id}_{\mathcal{X}} \in \mathcal{X}_{\mathrm{op}}$，结合律由函数复合的一般性质继承。对有限族 $\phi_1,\ldots,\phi_k\in\mathcal X_{\mathrm{op}}$，本卷按函数复合约定记

$$c_k=\phi_k\circ\cdots\circ\phi_1,$$

并在 $k=0$ 时取 $c_0=\mathrm{id}_{\mathcal X}$。这一记号只使用 $\mathcal X_{\mathrm{op}}$ 的幺半群结构；作为链来读取时见 § 4.1。

#### 诱导规范结构

对分量伪度量 $d_i \in \mathcal{G}$，定义 $\mathcal{X}_{\mathrm{op}}$ 上的**诱导算子伪度量**：

$$d_{\mathrm{op},i}(\phi, \psi) := \sup_{x \in \mathcal{X}} d_i(\phi(x), \psi(x))$$

记 $\mathcal{G}_{\mathrm{op}} = \{d_{\mathrm{op},i}\}_{i \in I}$。

> **约定（算子规范）**：除非另有说明，本书默认采用上述逐点上确界诱导的算子规范 $\mathcal G_{\mathrm{op}}$。

**命题 1.2（算子规范空间）**：$d_{\mathrm{op},i}$ 是 $\mathcal{X}_{\mathrm{op}}$ 上的扩展伪度量，$(\mathcal{X}_{\mathrm{op}}, \mathcal{G}_{\mathrm{op}}, \bot_{\mathrm{op}})$ 构成扩展规范空间。

**证明**：

- 非吸收部分非空：由 § 1.1，取 $z\in\mathcal X$ 且 $z\neq\bot$。恒等算子 $\mathrm{id}_{\mathcal X}$ 满足 $\mathrm{id}_{\mathcal X}(z)=z\neq\bot$，故 $\mathrm{id}_{\mathcal X}\neq\bot_{\mathrm{op}}$。
- 自距零：$d_{\mathrm{op},i}(\phi, \phi) = \sup_x d_i(\phi(x), \phi(x)) = 0$。
- 对称性：由 $d_i$ 的对称性逐点继承。
- 三角不等式：对任意 $x$，$d_i(\phi(x), \chi(x)) \leq d_i(\phi(x), \psi(x)) + d_i(\psi(x), \chi(x))$。取 $\sup_x$ 并用 $\sup(f+g) \leq \sup f + \sup g$ 即得。
- 吸收元隔离：对 $\phi \neq \bot_{\mathrm{op}}$，存在 $x_0 \in \mathrm{dom}(\phi)$，故 $d_{\mathrm{op},i}(\phi, \bot_{\mathrm{op}}) \geq d_i(\phi(x_0), \bot) = +\infty$。$\square$

> **注（定义域隔离）**：$\mathrm{dom}(\phi) \neq \mathrm{dom}(\psi)$ 蕴含 $d_{\mathrm{op},i}(\phi, \psi) = +\infty$（$\forall i \in I$）。
>
> **证明**：对称差非空，不失一般性取
>
> $$x_0 \in \mathrm{dom}(\phi) \setminus \mathrm{dom}(\psi).$$
>
> 则
>
> $$\psi(x_0)=\bot,\qquad d_i(\phi(x_0),\bot)=+\infty.$$
>
> 因而
>
> $$d_{\mathrm{op},i}(\phi,\psi)\ge d_i(\phi(x_0),\psi(x_0))=+\infty.$$
>
> 另一侧由 $d_{\mathrm{op},i}$ 的对称性给出。因而按定义域划分算子时，不同类在每个诱导分量下均相距 $+\infty$。$\square$

#### 受限评估

对 $U \subseteq \mathcal{X}$，记**受限评估**：

$$d_{\mathrm{op},i}(\phi, \psi)\big|_U := \sup_{x \in U} d_i(\phi(x), \psi(x))$$

当 $U=\emptyset$ 时，上确界按约定取 $0$。

> **注（受限评估的伪度量性质与局限）**：对固定 $U$，$d_{\mathrm{op},i}(\cdot, \cdot)\big|_U$ 满足自距零、对称、三角不等式（前三条扩展伪度量公理），并且恒有
>
> $$d_{\mathrm{op},i}(\phi, \psi)\big|_U \leq d_{\mathrm{op},i}(\phi, \psi).$$
>
> 但 $d_{\mathrm{op},i}(\cdot, \cdot)\big|_U$ 一般不满足吸收元隔离（公理 (iv)），因此作为推导工具使用，不一定构成 § 1.1 意义下的扩展规范空间。
>
> **证明**：前三条公理逐点继承，并在同一个 $U$ 上取上确界；全域上界由 $U\subseteq\mathcal{X}$ 直接给出。
>
> 若 $U=\emptyset$ 且 $\phi\neq\bot_{\mathrm{op}}$，则
>
> $$d_{\mathrm{op},i}(\phi,\bot_{\mathrm{op}})\big|_\emptyset=0,$$
>
> 不能给出 $+\infty$ 隔离。$\square$

> **注（受限评估的三角不等式）**：三角不等式只在固定同一个 $U$ 的受限评估中使用。当三项分别取不同限制域时，本书不把这些量视为同一个伪度量上的三角结构。受限评估将度量比较限定在特定子集（如上游像集或某个局部评估域），不计入 $U$ 外点的差异，因此可用于局部误差估计。

规范空间给出了点与集合的分辨量，诱导规范则使算子之间也可以作距离比较。下一章转而固定一个算子，研究输入的分量距离如何约束输出的分量距离。

### 1.4 习题

**习题 1.1（分量与联合区分）**：设 $U=\{a,b,c\}$ 由三个不同点组成，$\mathcal X=U\sqcup\{\bot\}$。在 $U$ 上定义两个函数

$$
q_1(a)=q_1(c)=0,\qquad q_1(b)=1,
$$

$$
q_2(a)=q_2(b)=0,\qquad q_2(c)=1,
$$

并令 $d_i(x,y)=|q_i(x)-q_i(y)|$（$i=1,2$，$x,y\in U$）。各分量均按吸收元隔离公理扩展到 $\mathcal X$，且 $d_i(\bot,\bot)=0$。

**(i)** 验证 $(\mathcal X,\{d_1,d_2\},\bot)$ 是扩展规范空间，并计算 $\mathcal N_1(1,U)$、$\mathcal N_2(1,U)$ 与 $\mathcal N_{\{1,2\}}(1,U)$。

**(ii)** 求 $\{(q_1(x),q_2(x)):x\in U\}$，并与 $q_1(U)\times q_2(U)$ 比较。

**习题 1.2（度量熵与精度）**：设 $m\ge2$，$0<\delta<1$，$U=\{a,b_1,\ldots,b_m\}$ 由 $m+1$ 个不同点组成，$\mathcal X=U\sqcup\{\bot\}$。规定 $d(x,x)=0$，且

$$
d(a,b_k)=d(b_k,a)=1,\qquad
d(b_k,b_\ell)=\delta\quad(k\ne\ell),
$$

并按吸收元隔离公理扩展到 $\mathcal X$。本题省略单分量下标。

**(i)** 验证 $d$ 在 $U$ 上是度量，并求所有 $\varepsilon>0$ 时的 $\mathcal N(\varepsilon,U)$ 与 $E_\varepsilon(U)$。

**(ii)** 固定 $\delta$，对 $0<\eta\le1-\delta$，求 $E_\delta(U)-E_{\delta+\eta}(U)$，并讨论它随 $m$ 的变化。

**习题 1.3（算子规范的两种选择）**：设 $U=\{x_1,\ldots,x_n\}$ 由 $n\ge2$ 个不同点组成，$\mathcal X=U\sqcup\{\bot\}$。在 $U$ 上取离散度量 $d(x,y)=1$（$x\ne y$），并按吸收元隔离公理扩展到 $\mathcal X$。本题省略单分量下标。对 $\phi,\psi\in\mathcal X_{\mathrm{op}}$，定义

$$
d_{\mathrm{op}}^{\mathrm{av}}(\phi,\psi)=\frac1n\sum_{x\in U}d(\phi(x),\psi(x)).
$$

**(i)** 验证默认算子伪度量满足

$$
d_{\mathrm{op}}(\phi,\psi)=\max_{x\in U}d(\phi(x),\psi(x)),
$$

并证明 $d_{\mathrm{op}}^{\mathrm{av}}$ 也使 $(\mathcal X_{\mathrm{op}},\{d_{\mathrm{op}}^{\mathrm{av}}\},\bot_{\mathrm{op}})$ 成为扩展规范空间。

**(ii)** 取不同的 $a,b\in U$。令 $\phi$ 在 $U$ 上恒取 $a$，$\psi$ 仅在 $x_1$ 处取 $b$、其余处取 $a$，$\chi$ 在 $U$ 上恒取 $b$，三个算子均保持 $\bot$。分别计算两种规范下 $\phi$ 与 $\psi$、$\phi$ 与 $\chi$ 的距离。
