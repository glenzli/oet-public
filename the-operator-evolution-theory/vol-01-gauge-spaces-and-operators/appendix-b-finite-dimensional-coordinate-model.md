
<a id="oet-a5195ee5769e4816"></a>

## 附录 B 有限维实坐标模型

在有限维实空间中，坐标差给出分量距离，选定范数则给出整体距离。配上吸收元后，这构成 [附录 A](<appendix-a-separating-gauge-specialization.md#user-content-oet-afec88a6c1c23422>) 所讨论的分离规范空间的一类具体模型。本附录借助矩阵、范数与导数，为正文中的距离界、覆盖数和零化半径建立具体的计算方法。

以下先从坐标规范与范数距离的联系出发，讨论集合的覆盖估计，再考察如何在适当条件下用导数构造距离上界，以及获得下界还需要什么条件。随后转向零化半径的坐标解释，最后比较复合中的真实导数与非负上界。


<a id="oet-f87662457a7d82d4"></a>

### B.1 坐标规范、范数与覆盖

设 $n\ge1$，$A\subseteq\mathbb R^n$ 非空，并取符号 $\bot\notin\mathbb R^n$。本附录沿用正文的空间记号，取

$$
\mathcal X=A\cup\{\bot\}.
$$

取指标集 $I=\{1,\ldots,n\}$。对 $i\in I$ 定义

$$
d_i(x,y)=
\begin{cases}
|x_i-y_i|,&x,y\in A,\\
0,&x=y=\bot,\\
+\infty,&\text{$x,y$ 中恰有一个等于 $\bot$}.
\end{cases}
$$

称 $\mathcal G=\{d_i\}_{i=1}^n$ 为 $\mathcal X$ 上的**坐标规范族**。

**定义（无穷范数）**：对 $v=(v_1,\ldots,v_n)\in\mathbb R^n$，定义

$$
\|v\|_\infty:=\max_{1\le i\le n}|v_i|.
$$


<a id="oet-98bad2ee358bf00b"></a>

**命题 B.1（坐标规范的分离性）**：$(\mathcal X,\mathcal G,\bot)$ 是分离扩展规范空间。对 $x,y\in A$，其全族复合度量满足

$$
d_I(x,y)
=
\max_{1\le i\le n}|x_i-y_i|
=
\|x-y\|_\infty.
$$

对每个 $i\in I$，单个分量 $d_i$ 分离 $\mathcal X$ 当且仅当坐标投影

$$
\pi_i\big|_A:A\to\mathbb R,
\qquad
\pi_i(x)=x_i
$$

为单射。

**证明**：$|x_i-y_i|$ 是第 $i$ 个坐标投影从 $\mathbb R$ 的通常距离拉回所得伪度量；加入 $\bot$ 后，自距、对称性、三角不等式与吸收元隔离均成立。若所有 $d_i(x,y)=0$，则 $x,y\in A$ 时全部坐标相等，从而 $x=y$；涉及 $\bot$ 时由吸收元隔离得到同样结论。全族复合度量公式由 $d_I$ 的定义得到。

对固定的 $i$，吸收元隔离已经区分 $\bot$ 与 $A$。而对 $x,y\in A$，$d_i(x,y)=0$ 当且仅当 $\pi_i(x)=\pi_i(y)$。因此，$d_i$ 分离 $\mathcal X$ 当且仅当 $\pi_i\big|_A$ 为单射。$\square$

由第一部分，[附录 A](<appendix-a-separating-gauge-specialization.md#user-content-oet-afec88a6c1c23422>) 的全部点值精确化结论适用于坐标规范空间。

坐标规范分别记录各分量的差异。为得到标量距离，设 $\|\cdot\|_*$ 是 $\mathbb R^n$ 上选定的任意范数。在 $\mathcal X$ 上定义扩展距离

$$
d_*(x,y)=
\begin{cases}
\|x-y\|_*,&x,y\in A,\\
0,&x=y=\bot,\\
+\infty,&\text{$x,y$ 中恰有一个等于 $\bot$}.
\end{cases}
$$

$d_*$ 是 $\mathcal X$ 上的扩展度量。由有限维范数等价定理，存在常数 $a_*,b_*>0$，使

$$
a_*\|v\|_\infty
\le
\|v\|_*
\le
b_*\|v\|_\infty
\qquad(v\in\mathbb R^n).
$$

这里把所有坐标开球的有限交及其任意并所成的拓扑称为坐标规范族 $\mathcal G$ 诱导的拓扑。

记 $\mathcal N_*(\varepsilon,S)$ 为 $d_*$ 下以 $S\subseteq A$ 内部点为中心的开球覆盖数。


<a id="oet-5cd365cd756cb93e"></a>

**命题 B.2（范数比较、拓扑与覆盖）**：在上述记号下，以下结论成立。

**(i) 球与覆盖数比较。** 对任意有限正数 $\varepsilon$，每个 $x\in A$ 都满足

$$
B_I\!\left(x,\frac{\varepsilon}{b_*}\right)
\subseteq B_*(x,\varepsilon)
\subseteq B_I\!\left(x,\frac{\varepsilon}{a_*}\right).
$$

并且，对任意 $S\subseteq A$，

$$
\mathcal N_I\!\left(\frac{\varepsilon}{a_*},S\right)
\le \mathcal N_*(\varepsilon,S)
\le \mathcal N_I\!\left(\frac{\varepsilon}{b_*},S\right).
$$

**(ii) 拓扑一致性。** 坐标规范族 $\mathcal G$、全族复合度量 $d_I$ 与任意 $d_*$ 在 $\mathcal X$ 上诱导相同的拓扑。

**(iii) 完备性。** $A$ 在 $d_*$ 下完备当且仅当 $A$ 是 $\mathbb R^n$ 的闭集。

**(iv) 紧致性。** $A$ 在 $d_*$ 下紧致当且仅当 $A$ 在 $\mathbb R^n$ 中闭且有界。

**证明**：

**(i)** 范数比较给出

$$
a_*d_I(x,y)\le d_*(x,y)\le b_*d_I(x,y)
\qquad(x,y\in A).
$$

分别代入两个严格距离条件，即得两侧球包含。将同一组内部中心的球放大，覆盖仍然成立，故得到覆盖数比较；没有有限覆盖时按 $+\infty$ 约定读取。

**(ii)** 由 $B_I(x,r)=\bigcap_{i\in I}B_i(x,r)$，每个 $d_I$-开球均为坐标规范拓扑中的开集。反之，若 $y\in B_i(x,r)$，则 $\rho=r-d_i(x,y)>0$，且三角不等式给出

$$
B_I(y,\rho)\subseteq B_i(x,r).
$$

所以坐标开球也是 $d_I$-开集。(i) 中的球包含又表明 $d_I$ 与 $d_*$ 在 $A$ 上诱导相同拓扑；$\bot$ 在各扩展距离下均为孤立点，故结论在 $\mathcal X$ 上成立。

**(iii)** 有限维赋范空间 $(\mathbb R^n,\|\cdot\|_*)$ 完备，其闭子集也完备；反之，度量空间中的完备子集必为闭集。范数等价保证这里的闭集与 $\mathbb R^n$ 通常拓扑下的闭集相同，故得到所述等价关系。

**(iv)** 范数等价保持紧致性与有界性。因此，由有限维空间的海涅–博雷尔定理，$A$ 在 $d_*$ 下紧致当且仅当它在 $\mathbb R^n$ 中闭且有界。$\square$

对标准欧氏范数 $\|\cdot\|_2$，任意 $v\in\mathbb R^n$ 都满足

$$
\|v\|_\infty^2
\le \sum_{i=1}^n|v_i|^2
=\|v\|_2^2
\le n\|v\|_\infty^2.
$$

两侧开平方，得到

$$
\|v\|_\infty
\le
\|v\|_2
\le
\sqrt n\,\|v\|_\infty.
$$

在这一欧氏情形中，比较常数可取 $a_*=1$、$b_*=\sqrt n$。

于是

$$
\mathcal N_I(\varepsilon,S)
\le
\mathcal N_{\mathrm{Euc}}(\varepsilon,S)
\le
\mathcal N_I\!\left(\frac{\varepsilon}{\sqrt n},S\right).
$$

这里 $\mathcal N_{\mathrm{Euc}}$ 表示欧氏距离

$$
d_{\mathrm{Euc}}(x,y)=\|x-y\|_2
$$

下的内覆盖数。下标 $\mathrm{Euc}$ 用于避免与第二个坐标伪度量 $d_2$ 混淆。选择其他范数不会改变有限维空间的拓扑，但可能改变上述比较常数以及由它们导出的定量界。


<a id="oet-6f0f018319c18266"></a>

**命题 B.3（有界盒中的坐标覆盖上界）**：设

$$
S\subseteq A\cap\prod_{i=1}^n[a_i,b_i]\subseteq\mathbb R^n,
\qquad a_i\le b_i,
$$

且 $\varepsilon>0$。则

$$
\mathcal N_I(\varepsilon,S)
\le
\prod_{i=1}^n
\left(
\left\lfloor\frac{b_i-a_i}{\varepsilon}\right\rfloor+1
\right).
$$

相应地，

$$
\mathcal N_{\mathrm{Euc}}(\varepsilon,S)
\le
\prod_{i=1}^n
\left(
\left\lfloor\frac{\sqrt n\,(b_i-a_i)}{\varepsilon}\right\rfloor+1
\right).
$$

**证明**：对第 $i$ 个区间取

$$
m_i=\left\lfloor\frac{b_i-a_i}{\varepsilon}\right\rfloor+1
$$

个等长子区间；当 $a_i=b_i$ 时只取一个退化子区间。每个非退化子区间的长度严格小于 $\varepsilon$。这些子区间的有限直积以至多 $\prod_i m_i$ 个坐标直径严格小于 $\varepsilon$ 的单元覆盖外部盒。从每个与 $S$ 相交的单元中选取一个 $S$ 内点作为中心，即得 $d_I$ 下的内覆盖。欧氏上界由

$$
\mathcal N_{\mathrm{Euc}}(\varepsilon,S)
\le
\mathcal N_I\!\left(\frac{\varepsilon}{\sqrt n},S\right)
$$

及第一式得到。$\square$


<a id="oet-a57e9e873735ed63"></a>

**命题 B.4（欧氏覆盖数的维数估计）**：取 $A=\mathbb R^n$，设 $\varepsilon>0$，并记

$$
\overline B_2(c,R)
=
\{x\in\mathbb R^n:\|x-c\|_2\le R\}.
$$

**(i) 仿射子空间内的有界集。** 设 $W\subseteq\mathbb R^n$ 为 $r$ 维线性子空间，$c\in\mathbb R^n$，$R\ge0$ 为有限实数。若非空集合 $S$ 满足

$$
S\subseteq(c+W)\cap\overline B_2(c,R),
$$

则

$$
\mathcal N_{\mathrm{Euc}}(\varepsilon,S)
\le
\left(1+\frac{2R}{\varepsilon}\right)^r.
$$

这里不要求 $S$ 闭或紧。当 $r=0$ 时，$S=\{c\}$，覆盖数为 $1$。

**(ii) 欧氏球的双侧界。** 对任意有限实数 $R>0$，

$$
\left(\frac R\varepsilon\right)^n
\le
\mathcal N_{\mathrm{Euc}}
\bigl(\varepsilon,\overline B_2(0,R)\bigr)
\le
\left(1+\frac{2R}{\varepsilon}\right)^n.
$$

**(iii) 线性像的秩上界。** 设 $T:\mathbb R^n\to\mathbb R^n$ 为秩 $r$ 的线性映射，$R\ge0$ 为有限实数，并令

$$
S_T=T\bigl(\overline B_2(0,R)\bigr).
$$

则

$$
\mathcal N_{\mathrm{Euc}}(\varepsilon,S_T)
\le
\left(
1+\frac{2\|T\|_{2\to2}R}{\varepsilon}
\right)^r.
$$

其中

$$
\|T\|_{2\to2}
:=\sup_{x\ne0}\frac{\|Tx\|_2}{\|x\|_2}
$$

为 $T$ 的**欧氏算子范数**，表示向量长度的最大放大倍数；下标 $2\to2$ 表示输入与输出均用欧氏范数衡量。

当 $r=0$ 时，右侧按 $a^0=1$ 读取，且 $S_T=\{0\}$。

**证明**：

**(i)** 若 $r=0$ 或 $R=0$，则非空性给出 $S=\{c\}$，结论成立。以下设 $r\ge1$ 且 $R>0$。任取有限集 $E\subseteq S$，要求不同点之间的距离不小于 $\varepsilon$。在仿射空间 $c+W$ 内，以 $E$ 中各点为中心、半径 $\varepsilon/2$ 的开球两两不交，并都包含于以 $c$ 为中心、半径 $R+\varepsilon/2$ 的开球。比较该空间中的 $r$ 维体积，并约去单位球体积，得到

$$
|E|\left(\frac\varepsilon2\right)^r
\le
\left(R+\frac\varepsilon2\right)^r,
\qquad
|E|\le\left(1+\frac{2R}{\varepsilon}\right)^r.
$$

这类有限集的可能基数构成非空、有界的自然数集合，因此可取基数最大的一个，记为 $E_\varepsilon$。若某点 $x\in S$ 不在以 $E_\varepsilon$ 为中心的半径 $\varepsilon$ 开球之并中，则它到每个中心的距离均不小于 $\varepsilon$，从而可加入 $E_\varepsilon$，与基数最大性矛盾。因此，这些开球覆盖 $S$，且中心全部位于 $S$，所得内覆盖即满足所述上界。

**(ii)** 上界由 (i) 取 $W=\mathbb R^n$、$c=0$ 得到。对下界，设 $N$ 个半径为 $\varepsilon$ 的欧氏开球覆盖 $\overline B_2(0,R)$。比较 Lebesgue 体积得到

$$
\operatorname{vol}_n\bigl(\overline B_2(0,R)\bigr)
\le
N\operatorname{vol}_n\bigl(B_2(0,\varepsilon)\bigr),
$$

故 $N\ge(R/\varepsilon)^n$。

**(iii)** $S_T$ 非空，位于 $r$ 维线性子空间 $\operatorname{im}(T)$ 中，且对 $\|x\|_2\le R$ 有

$$
\|Tx\|_2\le\|T\|_{2\to2}\|x\|_2
\le\|T\|_{2\to2}R.
$$

由 (i) 取 $W=\operatorname{im}(T)$、$c=0$，并以 $\|T\|_{2\to2}R$ 为半径，即得上界；$r=0$ 时 $T=0$，故 $S_T=\{0\}$。$\square$


<a id="oet-a81f07d81e16c501"></a>

### B.2 坐标 Lip 证书与范数估计

前面讨论了输入集合的覆盖数，下面考察算子如何传递点对距离，并用导数构造坐标 Lip 上界。

设 $O\subseteq\mathbb R^n$ 为开集，$F=(F_1,\ldots,F_n):O\to\mathbb R^n$ 连续可微，其中 $F_j:O\to\mathbb R$ 为第 $j$ 个输出坐标函数。取非空凸集 $U\subseteq A\cap O$，满足 $F(U)\subseteq A$，并定义算子 $\phi_F\in\mathcal X_{\mathrm{op}}$：

$$
\phi_F(x)=
\begin{cases}
F(x), & x\in U,\\
\bot, & x\in\mathcal X\setminus U.
\end{cases}
$$

于是 $\operatorname{dom}(\phi_F)=U$。

若对所有 $i,j\in I$，均有

$$
L_{i\to j}
:=
\sup_{z\in U}
\left|\frac{\partial F_j}{\partial x_i}(z)\right|
<+\infty,
$$

记 $\mathbf L=(L_{i\to j})_{i,j\in I}$。箭头左端表示输入、右端表示输出，$L_{i\to j}=[\mathbf L]_{ji}$ 位于第 $j$ 行、第 $i$ 列；以下带箭头下标的矩阵均沿用这一行列约定。通过有限非负实数到 $\bar{\mathbb R}_+$ 的自然嵌入，把 $\mathbf L$ 视为扩展非负实矩阵。


<a id="oet-454cb30cfc37f08c"></a>

**命题 B.5（Jacobi 分量上界给出坐标 Lip 矩阵）**：上述有限矩阵 $\mathbf L$ 属于

$$
\mathscr L(\phi_F)\big|_U.
$$

**证明**：固定 $x,y\in U$。由 $U$ 的凸性，线段 $x+t(y-x)$（$0\le t\le1$）包含于 $U$。对每个输出坐标 $j$，沿该线段应用微积分基本定理：

$$
F_j(y)-F_j(x)
=
\int_0^1
\sum_{i=1}^n
\frac{\partial F_j}{\partial x_i}(x+t(y-x))(y_i-x_i)\,dt.
$$

取绝对值并逐项使用导数上界，得到

$$
|F_j(y)-F_j(x)|
\le
\sum_{i=1}^n L_{i\to j}|y_i-x_i|.
$$

这正是坐标规范下的 Lip 矩阵不等式。$\square$

这一构造只给出一个合法上界证书，不声称 $\mathbf L$ 的条目在 $\mathscr L(\phi_F)\big|_U$ 中逐项最小。

以下对已声明逐条目有限的非负矩阵，进行实矩阵、实向量及范数运算时，将其自然识别为非负实矩阵，并沿用原记号。有限非负实数到 $\bar{\mathbb R}_+$ 的自然嵌入保持有限和、积与序关系，因此相应实数估计也可读作扩展值不等式。


<a id="oet-5386499e20ce893d"></a>

**命题 B.6（坐标 Lip 矩阵的范数聚合）**：设 $\phi\in\mathcal X_{\mathrm{op}}$，$U\subseteq\operatorname{dom}(\phi)$，并取逐条目有限的矩阵 $\mathbf L\in\mathscr L(\phi)\big|_U$。记

$$
\|\mathbf L\|_{\infty\to\infty}
=
\max_{j\in I}\sum_{i\in I}L_{i\to j}.
$$

则对任意 $x,y\in U$，

$$
d_*(\phi(x),\phi(y))
\le
\frac{b_*}{a_*}
\|\mathbf L\|_{\infty\to\infty}
d_*(x,y).
$$

若 $w_i>0$（$i\in I$），并取加权 $\ell^1$ 范数

$$
\|v\|_{1,w}=\sum_{i\in I}w_i|v_i|,
$$

把由该范数诱导的扩展距离记作 $d_{1,w}$，则可直接取标量证书

$$
L_{1,w}(\mathbf L)
=
\max_{i\in I}
\frac{1}{w_i}
\sum_{j\in I}w_jL_{i\to j}.
$$

即

$$
d_{1,w}(\phi(x),\phi(y))
\le
L_{1,w}(\mathbf L)d_{1,w}(x,y).
$$

在欧氏范数下还可取较精确的标量证书

$$
d_{\mathrm{Euc}}(\phi(x),\phi(y))
\le
\|\mathbf L\|_{2\to2}\,d_{\mathrm{Euc}}(x,y),
$$

其中 $\|\mathbf L\|_{2\to2}$ 是 $\mathbf L$ 的欧氏算子范数。

**证明**：由于 $x,y,\phi(x),\phi(y)$ 均属于 $A$，相关坐标距离有限；又因 $\mathbf L$ 逐条目有限，原 Lip 矩阵不等式可按上述约定读作实数不等式。对分量上界取最大值，得到

$$
\|\phi(x)-\phi(y)\|_\infty
\le
\|\mathbf L\|_{\infty\to\infty}
\|x-y\|_\infty.
$$

在两端使用 $a_*\|v\|_\infty\le\|v\|_*\le b_*\|v\|_\infty$ 即得第一式。

对加权 $\ell^1$ 范数，逐分量求和并交换有限求和次序，得到

$$
\begin{aligned}
\|\phi(x)-\phi(y)\|_{1,w}
&\le
\sum_{j\in I}w_j\sum_{i\in I}L_{i\to j}|x_i-y_i|\\
&=
\sum_{i\in I}
\left(\sum_{j\in I}w_jL_{i\to j}\right)|x_i-y_i|\\
&\le
L_{1,w}(\mathbf L)
\sum_{i\in I}w_i|x_i-y_i|.
\end{aligned}
$$

对欧氏范数，令 $u=(|x_i-y_i|)_i$、$v=(|\phi_j(x)-\phi_j(y)|)_j$。逐分量有 $0\le v\le\mathbf L u$，故

$$
\|v\|_2
\le
\|\mathbf L u\|_2
\le
\|\mathbf L\|_{2\to2}\|u\|_2.
$$

又有 $\|u\|_2=d_{\mathrm{Euc}}(x,y)$ 与 $\|v\|_2=d_{\mathrm{Euc}}(\phi(x),\phi(y))$。$\square$

坐标数增多时，一个输出分量的距离上界未必需要累加全部输入分量。若所选 Lip 证书的每行只有少量非零条目，便可用实际参与求和的条目数控制最大范数下的放大。

固定逐条目有限的非负矩阵 $\mathbf L$，记

$$
\operatorname{supp}_j(\mathbf L):=\{i\in I:L_{i\to j}>0\},
\qquad
s_{\mathrm{row}}(\mathbf L):=\max_{j\in I}|\operatorname{supp}_j(\mathbf L)|,
\qquad
L_{\max}:=\max_{i,j\in I}L_{i\to j}.
$$

称 $\operatorname{supp}_j(\mathbf L)$ 为输出分量 $j$ 的**输入上界支撑**。$s_{\mathrm{row}}(\mathbf L)$ 是各行非零条目数的最大值，$L_{\max}$ 是所选矩阵的最大条目。当 $\mathbf L$ 是 Lip 证书时，这些集合记录的是所选证书的正条目，不判定算子的实际分量依赖关系。


<a id="oet-36ae8406e21d3213"></a>

**推论 B.7（行支撑控制的距离上界）**：对任意逐条目有限的非负矩阵 $\mathbf L$，有

$$
\|\mathbf L\|_{\infty\to\infty}
\le s_{\mathrm{row}}(\mathbf L)L_{\max}.
$$

若 $\phi\in\mathcal X_{\mathrm{op}}$、$U\subseteq\operatorname{dom}(\phi)$ 且 $\mathbf L\in\mathscr L(\phi)\big|_U$，则对任意 $x,y\in U$，

$$
d_I(\phi(x),\phi(y))
\le s_{\mathrm{row}}(\mathbf L)L_{\max}d_I(x,y).
$$

**证明**：由于矩阵逐条目非负，对每个输出分量 $j$，

$$
\sum_{i\in I}L_{i\to j}
=\sum_{i\in \operatorname{supp}_j(\mathbf L)}L_{i\to j}
\le |\operatorname{supp}_j(\mathbf L)|L_{\max}
\le s_{\mathrm{row}}(\mathbf L)L_{\max}.
$$

最大范数下的诱导矩阵范数等于最大行和，对 $j$ 取最大值即得第一式。再由 [命题 B.6](<#user-content-oet-5386499e20ce893d>) 的范数聚合得到距离上界。$\square$

因此，若每行至多有 $s$ 个非零条目，且每个条目不超过 $\lambda\ge0$，便可用 $s\lambda$ 作为上述放大上界。与仅按维数得到的 $nL_{\max}$ 相比，行支撑计数将 $n$ 换成了 $s_{\mathrm{row}}(\mathbf L)\le n$。若一族不同维数的模型中，行支撑数和条目大小都有与维数无关的统一上界，则最大范数下的 Lip 上界也可统一控制；高维本身并不迫使它增大。已知全部条目时，直接计算最大行和还可得到更精确的估计。

这一结论依赖所选范数。其他范数下的非零计数估计及其差异见 [习题 B.2](<#mb-exercise-oet-f09514ceb9b32a5a>) 与 [习题 B.3](<#mb-exercise-oet-661612e2b84e7cff>)；若点对只有部分坐标发生变化，还可进一步缩小求和范围，见 [习题 B.5](<#mb-exercise-oet-ad5d1c84e576f84a>)。


<a id="oet-def6ef684420ce10"></a>

### B.3 正交块规范与导数证书

坐标分量可以合并为子空间块。$\mathbb R^n$ 取标准欧氏内积 $\langle\cdot,\cdot\rangle$。设

$$
\mathbb R^n
=
V_1\mathbin\perp\cdots\mathbin\perp V_r
$$

是非零线性子空间的正交直和分解，并令 $P_a:\mathbb R^n\to\mathbb R^n$ 为到 $V_a$ 的正交投影。对 $a\in H:=\{1,\ldots,r\}$，在 $\mathcal X$ 上定义

$$
d_{V_a}(x,y)
=
\begin{cases}
\|P_a(x-y)\|_2,&x,y\in A,\\
0,&x=y=\bot,\\
+\infty,&\text{$x,y$ 中恰有一个等于 $\bot$}.
\end{cases}
$$

称 $\mathcal G_V=\{d_{V_a}\}_{a\in H}$ 为该正交分解在 $\mathcal X$ 上诱导的**正交块规范族**。


<a id="oet-5258752592a614bf"></a>

**命题 B.8（正交块规范的分离性）**：$(\mathcal X,\mathcal G_V,\bot)$ 是分离扩展规范空间。对任意 $x,y\in A$，

$$
x-y=\sum_{a\in H}P_a(x-y),
\qquad
\|x-y\|_2^2
=
\sum_{a\in H}d_{V_a}(x,y)^2.
$$

若取 $r=n$ 及 $V_i=\operatorname{span}\{e_i\}$，其中 $(e_i)_{i=1}^n$ 是标准正交基，则

$$
d_{V_i}=d_i
\qquad(i\in I).
$$

**证明**：每个 $d_{V_a}$ 都是欧氏距离沿线性投影 $P_a$ 的拉回，因而在 $A$ 上为伪度量；加入 $\bot$ 后仍满足扩展伪度量公理和吸收元隔离。正交直和给出

$$
v=\sum_{a\in H}P_av,
\qquad
\|v\|_2^2=\sum_{a\in H}\|P_av\|_2^2
\qquad(v\in\mathbb R^n).
$$

若所有 $d_{V_a}(x,y)=0$，则 $x,y\in A$ 时有 $P_a(x-y)=0$（$a\in H$），故 $x-y=0$；涉及 $\bot$ 时由吸收元隔离分辨。最后，当 $V_i=\operatorname{span}\{e_i\}$ 时，

$$
P_i(x-y)=\langle x-y,e_i\rangle e_i=(x_i-y_i)e_i,
$$

所以 $\|P_i(x-y)\|_2=|x_i-y_i|$。$\square$

沿用 [§ B.2](<#user-content-oet-a81f07d81e16c501>) 开头给定的 $U$、$O$、$F$ 与 $\phi_F$，并使用上述正交分解。记 $DF(z):\mathbb R^n\to\mathbb R^n$ 为 $F$ 在 $z\in O$ 处的线性导数，其标准坐标矩阵为 Jacobi 矩阵，满足

$$
[DF(z)]_{ji}=\frac{\partial F_j}{\partial x_i}(z).
$$

这里 $z$ 是求导位置，$DF(z)v$ 表示输入扰动 $v$ 对应的一阶输出变化。对 $a,b\in H$，定义

$$
L^V_{a\to b}
:=
\sup_{z\in U}
\|P_b\circ DF(z)\circ P_a\|_{2\to2},
$$

并假设所有 $L^V_{a\to b}$ 均有限。记 $\mathbf L^V=(L^V_{a\to b})_{a,b\in H}$，并通过自然嵌入把它视为扩展非负实矩阵。

对扰动向量 $v\in\mathbb R^n$，

$$
\bigl(P_b\circ DF(z)\circ P_a\bigr)v=P_b\bigl(DF(z)(P_av)\bigr).
$$

右侧从内向外依次取输入块 $V_a$、计算一阶输出变化、取输出块 $V_b$；求导位置 $z$ 始终不变。因此，$L^V_{a\to b}$ 统一控制 $U$ 上从输入块 $V_a$ 到输出块 $V_b$ 的导数放大。


<a id="oet-460dce986b592798"></a>

**命题 B.9（Jacobi 块上界给出正交块 Lip 证书）**：对任意 $x,y\in U$ 与 $b\in H$，

$$
d_{V_b}(F(x),F(y))
\le
\sum_{a\in H}L^V_{a\to b}d_{V_a}(x,y).
$$

因此，$\mathbf L^V$ 是正交块规范族 $\mathcal G_V$ 下的 Lip 矩阵。若取一维标准坐标分解，则块证书还原为 [§ B.2](<#user-content-oet-a81f07d81e16c501>) 开头由导数构造的坐标证书，即

$$
L^V_{i\to j}
=
\sup_{z\in U}
\left|
\frac{\partial F_j}{\partial x_i}(z)
\right|
=
L_{i\to j}.
$$

**证明**：固定 $x,y\in U$，并令 $z_t=x+t(y-x)$。由 $U$ 的凸性，$z_t\in U$（$0\le t\le1$）。微积分基本定理与正交分解给出

$$
\begin{aligned}
P_b(F(y)-F(x))
&=
\int_0^1\bigl(P_b\circ DF(z_t)\bigr)(y-x)\,dt\\
&=
\sum_{a\in H}
\int_0^1\bigl(P_b\circ DF(z_t)\circ P_a\bigr)(y-x)\,dt.
\end{aligned}
$$

由于 $P_a^2=P_a$，上式中的算子 $P_b\circ DF(z_t)\circ P_a$ 作用于 $y-x$ 与作用于 $P_a(y-x)$ 的结果相同。再由三角不等式和 $L^V_{a\to b}$ 的定义，

$$
\begin{aligned}
\|P_b(F(y)-F(x))\|_2
&\le
\sum_{a\in H}
\int_0^1
\bigl\|\bigl(P_b\circ DF(z_t)\circ P_a\bigr)(y-x)\bigr\|_2\,dt\\
&\le
\sum_{a\in H}
L^V_{a\to b}\|P_a(y-x)\|_2.
\end{aligned}
$$

这正是所需的正交块 Lip 不等式。一维标准坐标分解下，$P_j\circ DF(z)\circ P_i$ 的欧氏算子范数等于 $|\partial F_j/\partial x_i(z)|$。$\square$


<a id="oet-93bf7093aa284ce2"></a>

### B.4 范数下界与双侧估计

上面的估计控制输出差异至多放大多少。下面转向范数下界，并区分坐标 co-Lip 证书、全局距离下界与逐点导数下界。


<a id="oet-69edb7c1cac5d49b"></a>

**命题 B.10（坐标 co-Lip 证书与范数下界）**：

**(i) 坐标证书给出范数下界。** 设 $\phi\in\mathcal X_{\mathrm{op}}$，$\emptyset\neq U\subseteq\operatorname{dom}(\phi)$，并取逐条目有限的矩阵 $\mathbf K\in\mathscr K(\phi)\big|_U$。记

$$
\kappa
:=
\min_{i\in I}\max_{j\in I}K_{i\to j}.
$$

这里先对每个输入坐标 $i$ 取最大的下界条目，再在输入坐标之间取最小值；取得最大值的输出坐标 $j$ 可以随 $i$ 改变。

对任意 $x,y\in U$，

$$
\|\phi(x)-\phi(y)\|_\infty
\ge
\kappa\|x-y\|_\infty,
$$

从而

$$
d_*(\phi(x),\phi(y))
\ge
\frac{a_*}{b_*}\,
\kappa
d_*(x,y).
$$

若 $\kappa>0$，则 $\phi$ 在 $U$ 上单射。

特别地，在欧氏范数下可取下界常数 $\kappa/\sqrt n$。

**(ii) 逆向一般不成立。** 取 $n=2$、$A=\mathbb R^2$。存在欧氏等距映射 $R:\mathbb R^2\to\mathbb R^2$，使得算子 $\phi_R\in\mathcal X_{\mathrm{op}}$（在 $\mathbb R^2$ 上等于 $R$，在 $\bot$ 处取 $\bot$）的每个合法坐标 co-Lip 矩阵 $\mathbf K\in\mathscr K(\phi_R)\big|_{\mathbb R^2}$ 都是零矩阵。因此，正的欧氏距离下界不保证存在非零坐标 co-Lip 证书。

**证明**：

**(i)** 由于 $\mathbf K$ 逐条目有限，且 $U$ 中点及其像的坐标距离均有限，co-Lip 矩阵不等式可按上述约定读作实数不等式。取 $i_0\in I$ 使

$$
|x_{i_0}-y_{i_0}|=\|x-y\|_\infty.
$$

对任意 $j\in I$，co-Lip 不等式给出

$$
|\phi_j(x)-\phi_j(y)|
\ge
K_{i_0\to j}|x_{i_0}-y_{i_0}|.
$$

对 $j$ 取最大值得第一式。再用范数等价不等式

$$
\|\phi(x)-\phi(y)\|_*
\ge a_*\|\phi(x)-\phi(y)\|_\infty,
\qquad
\|x-y\|_\infty\ge\frac1{b_*}\|x-y\|_*,
$$

得到第二式。若 $x\ne y$ 且 $\kappa>0$，右端严格为正，故 $\phi(x)\ne\phi(y)$。在欧氏情形中代入 $a_*=1$、$b_*=\sqrt n$，得到所述常数。

**(ii)** 在 $\mathbb R^2$ 上定义

$$
R(x_1,x_2)
=
\frac1{\sqrt2}(x_1-x_2,x_1+x_2).
$$

令 $\phi_R$ 在 $\mathbb R^2$ 上等于 $R$，在 $\bot$ 处取 $\bot$。$R$ 是正交线性映射，故

$$
\|R(x)-R(y)\|_2=\|x-y\|_2.
$$

设 $\mathbf K\in\mathscr K(\phi_R)\big|_{\mathbb R^2}$。对差向量 $(1,1)$，第一个输出坐标差为零，因此

$$
0\ge K_{1\to1}+K_{2\to1},
$$

由非负性得 $K_{1\to1}=K_{2\to1}=0$。对差向量 $(1,-1)$，第二个输出坐标差为零，同理得到

$$
K_{1\to2}=K_{2\to2}=0.
$$

故 $\mathbf K=0$。$\square$

对于仿射算子，全空间上的最优双侧界可以由其线性部分精确计算。


<a id="oet-e1bc9665adf4aeca"></a>

**命题 B.11（仿射算子的欧氏双侧界）**：设 $F:\mathbb R^n\to\mathbb R^n$ 为仿射算子，$F(x)=Tx+b$，其中 $T$ 为线性映射，$b\in\mathbb R^n$。记 $\sigma_{\max}(T)$ 与 $\sigma_{\min}(T)$ 分别为 $T$ 的最大与最小奇异值。

**(i) 双侧界与最优常数。** 存在有限常数 $0\le k\le\ell$，使对任意 $x,y\in\mathbb R^n$，

$$
k\|x-y\|_2
\le
\|F(x)-F(y)\|_2
\le
\ell\|x-y\|_2.
$$

在全空间上，最小可取的上界常数与最大可取的下界常数分别为

$$
\ell=\sigma_{\max}(T),
\qquad
k=\sigma_{\min}(T).
$$

$F$ 单射当且仅当 $\sigma_{\min}(T)>0$。将 $F$ 限制到任意子集 $U\subseteq\mathbb R^n$ 时，这两个常数仍给出合法的双侧界，但未必最优。

**(ii) 正交换基不变性。** 设 $Q_{\mathrm{in}},Q_{\mathrm{out}}$ 为正交矩阵，并令 $T'=Q_{\mathrm{out}}TQ_{\mathrm{in}}^{\mathsf T}$。则 $T'$ 与 $T$ 的奇异值相同，因而以 $T'$ 为线性部分的仿射算子与 $F$ 具有相同的最优欧氏双侧常数；坐标条目的绝对值矩阵及其非零支撑一般不保持。

**证明**：(i) 对 $v=x-y\ne0$，

$$
\frac{\|F(x)-F(y)\|_2}{\|x-y\|_2}
=
\frac{\|Tv\|_2}{\|v\|_2}.
$$

当 $x,y$ 遍历全空间时，$v$ 遍历全部非零向量。因此，距离比的最大值与最小值就是单位球面上 $\|Tv\|_2$ 的最大值与最小值，分别为 $\sigma_{\max}(T)$ 与 $\sigma_{\min}(T)$，所述双侧界及其最优性随即成立。最小奇异值为正等价于 $\ker T=\{0\}$，也即 $F$ 单射。限制到 $U$ 后只减少可取的点对，故两侧界仍成立，但未必最优。

(ii) 由

$$
(T')^{\mathsf T}T'=Q_{\mathrm{in}}T^{\mathsf T}TQ_{\mathrm{in}}^{\mathsf T}
$$

可知 $(T')^{\mathsf T}T'$ 与 $T^{\mathsf T}T$ 正交相似，故奇异值相同，再由 (i) 得最优双侧常数不变。另一方面，取

$$
T=\begin{pmatrix}1&0\\0&0\end{pmatrix},
\qquad
Q=\frac1{\sqrt2}\begin{pmatrix}1&-1\\1&1\end{pmatrix},
$$

则 $T$ 只有一个非零条目，而 $QTQ^{\mathsf T}=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix}$ 有四个非零条目，条目绝对值也发生改变。$\square$

在凸域上，连续可微映射的输出差可以沿连接两输入的线段积分得到。对不同的输入 $x,y$，令 $v=y-x$，积分中的向量是 $DF(x+tv)v$。仅控制这些向量的长度，不能排除它们因方向变化而相互抵消。下面给出一种充分条件：让这些向量在同一输入方向 $v$ 上始终保留足够大的正向分量。


<a id="oet-3e4095f278f5ea6b"></a>

**命题 B.12（导数下界与全局 co-Lip）**：

**(i) 沿输入方向的正向分量给出全局下界。** 设 $U\subseteq\mathbb R^n$ 为非空凸集，$O\subseteq\mathbb R^n$ 为包含 $U$ 的开集，$F:O\to\mathbb R^n$ 连续可微。若存在 $\mu>0$，使

$$
\bigl\langle DF(z)v,v\bigr\rangle
\ge
\mu\|v\|_2^2
\qquad
(\forall z\in U,\ \forall v\in\mathbb R^n),
$$

则对任意 $x,y\in U$，

$$
\|F(x)-F(y)\|_2
\ge
\mu\|x-y\|_2.
$$

因而 $F\big|_U$ 单射。当 $v\ne0$ 时，$DF(z)v$ 在单位方向 $v/\|v\|_2$ 上的有向投影为 $\langle DF(z)v,v\rangle/\|v\|_2$；题设要求这一投影至少为 $\mu\|v\|_2$。上述条件也就是导数的二次型下界，只取决于 $DF(z)$ 的对称部。

**(ii) 仅有导数长度的下界仍然不足。** 存在非空凸开集 $U\subseteq\mathbb R^2$ 及连续可微映射 $F:U\to\mathbb R^2$，满足

$$
\|DF(z)v\|_2\ge\|v\|_2
\qquad(\forall z\in U,\ \forall v\in\mathbb R^2),
$$

但 $F$ 不单射，因而不存在正的全局 co-Lip 下界。由于最小奇异值是单位输入方向上导数长度的最小值，上述条件等价于 $\sigma_{\min}(DF(z))\ge1$（$z\in U$）。因此，(i) 中对正向分量的控制不能弱化为仅对长度的控制。

**证明**：(i) 固定 $x,y\in U$，令 $v=y-x$。由 $U$ 的凸性，$x+tv\in U$（$0\le t\le1$）。微积分基本定理给出

$$
F(y)-F(x)
=
\int_0^1DF(x+tv)v\,dt.
$$

与 $v$ 取内积并使用题设下界，得到

$$
\begin{aligned}
\bigl\langle F(y)-F(x),v\bigr\rangle
&=
\int_0^1
\bigl\langle DF(x+tv)v,v\bigr\rangle\,dt\\
&\ge
\mu\|v\|_2^2.
\end{aligned}
$$

另一方面，由 Cauchy-Schwarz 不等式，

$$
\bigl\langle F(y)-F(x),v\bigr\rangle
\le
\|F(y)-F(x)\|_2\|v\|_2.
$$

当 $x=y$ 时结论直接成立；当 $x\ne y$ 时，除以 $\|v\|_2>0$ 即得所需 co-Lip 下界。若 $F(x)=F(y)$，该下界与 $\mu>0$ 进一步给出 $x=y$。

最后，由转置的定义和实欧氏内积的对称性，对任意 $z\in U$ 与 $v\in\mathbb R^n$，有

$$
\langle DF(z)^{\mathsf T}v,v\rangle
=\langle v,DF(z)v\rangle
=\langle DF(z)v,v\rangle.
$$

再利用内积的线性性，得到

$$
\begin{aligned}
\left\langle\frac{DF(z)+DF(z)^{\mathsf T}}2v,v\right\rangle
&=\frac12\bigl(\langle DF(z)v,v\rangle
+\langle DF(z)^{\mathsf T}v,v\rangle\bigr)\\
&=\langle DF(z)v,v\rangle.
\end{aligned}
$$

因此，该二次型只依赖 Jacobi 矩阵的对称部，不要求 $DF(z)$ 本身对称。

(ii) 取非空凸开集及其上的映射

$$
U=(0,1)\times(0,4\pi),
\qquad
F(s,t)=e^s(\cos t,\sin t).
$$

$F$ 连续可微，直接计算得

$$
DF(s,t)
=
e^s
\begin{pmatrix}
\cos t&-\sin t\\
\sin t&\cos t
\end{pmatrix}.
$$

矩阵的第二个因子正交，故对任意 $v\in\mathbb R^2$，

$$
\|DF(s,t)v\|_2=e^s\|v\|_2\ge\|v\|_2.
$$

两个奇异值也均为 $e^s\ge1$。然而，取

$$
x=\left(\frac12,\pi\right),
\qquad
y=\left(\frac12,3\pi\right),
$$

则 $x,y\in U$，$F(x)=F(y)$，而 $\|x-y\|_2=2\pi>0$。任意正的 co-Lip 常数 $\kappa$ 都会给出 $0\ge2\pi\kappa>0$，矛盾。$\square$

这里导数的正交因子随位置旋转，沿线段积分时向量贡献可以抵消；二次型下界控制同一输入差方向上的投影，避免了这种抵消。


<a id="oet-ad3957f2de83d301"></a>

### B.5 坐标模型中的零化半径

距离界控制输出变化的大小，零化半径则检查多大的输入球内输出保持零距。在坐标模型中，输出分量零距就是坐标值相等，计算纤维因而是相应的水平集。

取非空 $U\subseteq A$ 及映射 $F:U\to A$，沿用前述延拓记号 $\phi_F$。对基点 $y\in U$ 和坐标 $i,j\in I$，有限正数 $r$ 是 $r^{\mathrm N}_{\phi_F,i,j}(y\mid U)$ 的合法半径，恰好意味着

$$
\forall x\in U,\quad |x_i-y_i|<r\Longrightarrow F_j(x)=F_j(y).
$$

该零化半径就是所有合法半径的上确界。全族输入、全族输出的情形，只需把输入条件换为 $\|x-y\|_\infty<r$，把输出条件换为 $F(x)=F(y)$。

单坐标输入条件限制的是条带与 $U$ 的交，其余坐标仍可变化，因此不能只检查沿第 $i$ 个方向的导数。全族输入条件则限制基点周围的小球与 $U$ 的交，正半径要求输出在该交集上精确常值。评估域可能位于低维仿射子空间中；计算仿射映射在其上的作用时，先记录域内点差张成的方向。

**定义（集合的方向空间）**：对非空集合 $U\subseteq\mathbb R^n$，记

$$
W_U:=\operatorname{span}\{x-y:x,y\in U\}.
$$


<a id="oet-5327d971cf04c4ca"></a>

**引理 B.13（受限仿射映射的方向空间）**：设 $U\subseteq\mathbb R^n$ 非空，且 $F(x)=Tx+b$。则

$$
W_{F(U)}=T(W_U),
\qquad
F_j\big|_U\text{ 为常值}
\quad\Longleftrightarrow\quad
T_{j\bullet}\big|_{W_U}=0.
$$

若另一仿射映射 $G(x)=Sx+c$ 在 $U$ 上与 $F$ 相同，则 $T|_{W_U}=S|_{W_U}$。因此 $\operatorname{rank}(T|_{W_U})=\dim W_{F(U)}$ 由受限映射 $F|_U$ 决定。

**证明**：对任意 $x,y\in U$，有

$$
F(x)-F(y)=T(x-y).
$$

对两侧的点差集合取线性张成，利用线性映射保持有限线性组合，得到 $W_{F(U)}=T(W_U)$。第 $j$ 个输出坐标在 $U$ 上为常值，当且仅当 $T_{j\bullet}(x-y)=0$ 对所有 $x,y\in U$ 成立；这又等价于该线性泛函在这些点差的张成空间 $W_U$ 上为零。

若 $F|_U=G|_U$，则 $(T-S)(x-y)=0$ 对所有域内点对成立。再次取线性张成，得到 $(T-S)|_{W_U}=0$。限制映射的秩等于其像空间的维数，故最后的等式与扩展无关性随之成立。$\square$


<a id="oet-055e3702cf9c3930"></a>

**命题 B.14（零化半径与导数）**：取 $A=\mathbb R^n$，设 $U\subseteq\mathbb R^n$ 非空，$F:U\to\mathbb R^n$，并固定 $y\in U$。沿用 $\phi_F$ 在 $U$ 上等于 $F$、在 $\mathcal X\setminus U$ 上等于 $\bot$ 的约定。

**(i)** 若 $U$ 是开集且 $F$ 在 $y$ 可微，则

$$
r^{\mathrm N}_{\phi_F,d_I,I}(y\mid U)>0\quad\Longrightarrow\quad DF(y)=0.
$$

反向一般不成立。

**(ii)** 若 $U$ 为凸集或开集，且 $F(x)=Tx+b$，其中 $T$ 为 $n\times n$ 实矩阵、$b\in\mathbb R^n$，则

$$
r^{\mathrm N}_{\phi_F,d_I,I}(y\mid U)
=
\begin{cases}
+\infty,&T|_{W_U}=0,\\
0,&T|_{W_U}\ne0.
\end{cases}
$$

对任意 $i,j\in I$，记 $T_{j\bullet}$ 为 $T$ 的第 $j$ 行，则

$$
r^{\mathrm N}_{\phi_F,i,j}(y\mid U)
=
\begin{cases}
+\infty,&T_{j\bullet}|_{W_U}=0,\\
0,&T_{j\bullet}|_{W_U}\ne0.
\end{cases}
$$

上述值与基点 $y$ 无关，因而也分别等于在 $U$ 上的统一零化半径。单输出坐标的判定取决于对应行在 $W_U$ 上的限制，与所选输入坐标 $i$ 无关。

当 $U$ 是开集时，$W_U=\mathbb R^n$，判定分别化为 $T=0$ 与 $T_{j\bullet}=0$；在低维凸域上，非零矩阵或非零行也可能在 $W_U$ 上消失。

**证明**：**(i)** 正零化半径意味着合法半径集合的上确界为正，因而其中存在某个正半径 $r$。又因 $U$ 开，存在 $s>0$ 使 $B_I(y,s)\subseteq U$。因此 $F$ 在 $B_I(y,\min\{r,s\})$ 上恒等于 $F(y)$，从而 $DF(y)=0$。

为说明反向不成立，取 $n=1$、$U=\mathbb R$、$F(t)=t^2$。此时 $F'(0)=0$；但对任意 $r>0$，均存在 $0<|t|<r$ 使 $F(t)\ne F(0)$。故基点 $0$ 处没有合法正半径，零化半径为 $0$。

**(ii)** 先设 $U$ 凸。由 [引理 B.13](<#user-content-oet-5327d971cf04c4ca>)，$T|_{W_U}=0$ 恰好表示 $F$ 在 $U$ 上为常值；相应地，$T_{j\bullet}|_{W_U}=0$ 恰好表示 $F_j$ 在 $U$ 上为常值。此时所有有限正半径均合法，对应半径为 $+\infty$。

若 $F_j$ 不为常值，则对任意基点 $y\in U$，存在 $z\in U$ 使 $F_j(z)\ne F_j(y)$。对 $0<t\le1$，由凸性有 $x_t=y+t(z-y)\in U$，且

$$
|(x_t)_i-y_i|=t|z_i-y_i|,
\qquad
F_j(x_t)-F_j(y)=t\bigl(F_j(z)-F_j(y)\bigr)\ne0.
$$

给定任意 $r>0$，取充分小的 $t>0$，即得输入坐标距离小于 $r$、输出坐标仍不同的点。因此单坐标半径为 $0$。若 $F$ 不为常值，取 $F(z)\ne F(y)$，用同一线段及 $\|x_t-y\|_\infty=t\|z-y\|_\infty$，同理得到全族半径为 $0$。

再设 $U$ 是开集。取域内一点及其小邻域，各坐标方向上的小位移都属于 $U-U$，故 $W_U=\mathbb R^n$。当 $T\ne0$ 时，由 (i) 及 $DF(y)=T$ 得到全族半径为 $0$。当 $T_{j\bullet}\ne0$ 时，取 $k$ 使 $T_{jk}\ne0$。对任意 $r>0$，可取充分小的 $0<t<r$ 使 $x=y+te_k\in U$，此时 $|x_i-y_i|\le t<r$ 而 $F_j(x)-F_j(y)=tT_{jk}\ne0$。零矩阵或零行的情形仍由常值性给出 $+\infty$。

各点态值在非空 $U$ 上相同，取下确界就得到相应的统一半径。$\square$

纤维中存在可变方向，并不保证它包含基点周围的小球；[习题 B.7](<#mb-exercise-oet-291a10c8f6ac11cb>) 用二维投影说明这一区别。下面转向复合，考察真实导数中的通道相消。


<a id="oet-3bd1141a17ae9755"></a>

### B.6 复合导数与通道相消

复合导数保留各通道项的符号，而非负上界舍弃了这些符号。两者虽都使用矩阵乘积，对通道非零性的判断却不同。

设 $k\ge1$，$F_m:O_m\to\mathbb R^n$（$1\le m\le k$）连续可微，其中 $O_m\subseteq\mathbb R^n$ 为开集。从 $x_0\in O_1$ 出发，递归令 $x_m=F_m(x_{m-1})$，并假设 $x_{m-1}\in O_m$ 对每一步都成立。记

$$
C_k=F_k\circ\cdots\circ F_1,
\qquad A_m=DF_m(x_{m-1}),
$$

并用 $|A|$ 表示矩阵 $A$ 逐条目取绝对值所得的非负矩阵。


<a id="oet-8b08064a80bd8c55"></a>

**命题 B.15（复合导数的上界与相消）**：在上述条件下，

$$
DC_k(x_0)=A_k\cdots A_1,
\qquad
\bigl|DC_k(x_0)\bigr|\le |A_k|\cdots|A_1|,
$$

其中不等式按条目成立。右侧某个条目严格为正，并不保证左侧对应条目非零。

**证明**：由各 $O_m$ 开放及 $F_m$ 连续，可逐步缩小 $x_0$ 的开邻域，使全部中间复合落在下一步定义域内。链式法则给出第一式。矩阵乘积的每个条目是经过中间指标的通道乘积之和；对该和使用三角不等式，即得第二式。

为说明非负上界为正时真实条目仍可为零，取两步线性映射 $F_1(x)=A_1x$、$F_2(x)=A_2x$，其中

$$
A_1=\begin{pmatrix}1&0\\-1&1\end{pmatrix},
\qquad
A_2=\begin{pmatrix}1&1\\0&1\end{pmatrix}.
$$

直接计算得

$$
[A_2A_1]_{1\to1}=1\cdot1+1\cdot(-1)=0,
\qquad
[|A_2||A_1|]_{1\to1}=1\cdot1+1\cdot1=2.
$$

两个非零通道项在真实导数中相互抵消，逐项绝对值上界则保留了它们的大小。$\square$

这里的 $A_m$ 是轨迹点处的导数值，不能直接替代整个实际输入域上的距离证书。取得各步合法的 Lip 或 co-Lip 证书后，其复合直接使用 [推论 2.5](<02-operator-bounds.md#user-content-oet-c80171fa685dc795>)；网络路径上的作用范围见 [命题 5.11](<05-operator-networks.md#user-content-oet-d64105c6ec192365>)。

坐标、范数、正交投影与导数由此为卷 1 的分量语言提供了具体的计算方法：上界可由导数构造并沿链复合，下界须检查相应的全局条件；计算纤维成为所选输出分量的共同水平集，零化半径则检查这些分量在输入球与实际输入域的交集上是否保持精确常值。具体数值界取决于所选范数、坐标与正交分块；应用于网络时，还须核对证书所适用的实际输入域与路径域。


<a id="oet-5bda2e1ea20d6a35"></a>

### B.7 习题

**定义（坐标差支撑）**：对 $x,y\in A$，定义

$$
\operatorname{supp}(x-y):=\{i\in I:x_i\ne y_i\}.
$$

以下习题沿用这一记号，它记录点对之间实际发生变化的坐标。


<div data-mb-exercise="oet-1873ded007b293ec">

**习题 B.1（正交坐标支撑的欧氏界）**：在 [§ B.1](<#user-content-oet-f87662457a7d82d4>) 的坐标规范空间中，设 $n\ge1$、$A\subseteq\mathbb R^n$ 非空，$I=\{1,\ldots,n\}$。对 $x,y\in A$，记 $d_i(x,y)=|x_i-y_i|$、$d_I(x,y)=\max_{i\in I}d_i(x,y)$、$d_{\mathrm{Euc}}(x,y)=\|x-y\|_2$。证明

$$
d_{\mathrm{Euc}}(x,y)^2
=
\sum_{i\in\operatorname{supp}(x-y)}d_i(x,y)^2,
$$

并由此推出

$$
d_{\mathrm{Euc}}(x,y)
\le
\sqrt{|\operatorname{supp}(x-y)|}\,d_I(x,y).
$$

</div>



<div data-mb-exercise="oet-f09514ceb9b32a5a">

**习题 B.2（非零计数与其他范数）**：设 $\mathbf L$ 为逐条目有限的非负矩阵，沿用正文的 $L_{\max}$，并记

$$
c:=\max_{i\in I}|\{j\in I:L_{i\to j}>0\}|,
\qquad
m:=|\{(i,j)\in I^2:L_{i\to j}>0\}|.
$$

**(i)** 证明

$$
\|\mathbf L\|_{1\to1}\le cL_{\max},
\qquad
\|\mathbf L\|_{2\to2}\le\sqrt m\,L_{\max}.
$$

其中 $\|\cdot\|_{1\to1}$ 是由未加权的 $\ell^1$ 范数诱导的矩阵范数。

**(ii)** 若 $\phi\in\mathcal X_{\mathrm{op}}$、$U\subseteq\operatorname{dom}(\phi)$ 且 $\mathbf L\in\mathscr L(\phi)\big|_U$，证明对任意 $x,y\in U$，

$$
d_{\mathrm{Euc}}(\phi(x),\phi(y))
\le\sqrt m\,L_{\max}d_{\mathrm{Euc}}(x,y).
$$

</div>



<div data-mb-exercise="oet-661612e2b84e7cff">

**习题 B.3（低非零比例与欧氏放大）**：对每个 $n\ge1$，取 $I=\{1,\ldots,n\}$，定义非负实矩阵 $\mathbf B_n$：

$$
(B_n)_{i\to j}=
\begin{cases}
1,&i=1,\\
0,&i\ne1.
\end{cases}
$$

它的第一列全为 $1$，其余列全为 $0$。证明其非零条目数为 $n$，占全部条目的比例为 $1/n$，而

$$
\|\mathbf B_n\|_{\infty\to\infty}=1,
\qquad
\|\mathbf B_n\|_{2\to2}=\sqrt n.
$$

据此说明：即使条目均不超过 $1$、非零比例随维数趋于零，欧氏算子范数也未必有与维数无关的上界；这与 [推论 B.7](<#user-content-oet-36ae8406e21d3213>) 并不矛盾。

</div>



<div data-mb-exercise="oet-4f0e5a8aa7221640">

**习题 B.4（零块证书下的分量解耦）**：在 [命题 B.9](<#user-content-oet-460dce986b592798>) 的条件下，证明下列结论。

**(i)** 若 $a,b\in H$ 满足 $L^V_{a\to b}=0$，且 $x,y\in U$ 满足 $x-y\in V_a$，则

$$
P_bF(x)=P_bF(y).
$$

**(ii)** 若对固定的 $a\in H$ 有

$$
L^V_{a\to b}=0
\qquad(b\in H,\ b\ne a),
$$

则任意满足 $x-y\in V_a$ 的 $x,y\in U$ 都满足

$$
F(x)-F(y)\in V_a.
$$

</div>



<div data-mb-exercise="oet-ad5d1c84e576f84a">

**习题 B.5（证书支撑交叠下的分量传播界）**：在本附录的坐标规范空间中，设 $\phi\in\mathcal X_{\mathrm{op}}$、$U\subseteq\operatorname{dom}(\phi)$，并取逐条目有限的 Lip 矩阵 $\mathbf L\in\mathscr L(\phi)\big|_U$。按 [§ B.2](<#user-content-oet-a81f07d81e16c501>) 的定义，记其输入上界支撑为 $\operatorname{supp}_j(\mathbf L)$，最大条目为 $L_{\max}$；坐标差支撑采用本节记号。证明对任意 $x,y\in U$ 与 $j\in I$，

$$
d_j(\phi(x),\phi(y))
\le
L_{\max}\,
|\operatorname{supp}_j(\mathbf L)\cap\operatorname{supp}(x-y)|
\,d_I(x,y).
$$

并由此推出

$$
d_I(\phi(x),\phi(y))
\le
L_{\max}
\max_{j\in I}
|\operatorname{supp}_j(\mathbf L)\cap\operatorname{supp}(x-y)|
\,d_I(x,y).
$$

</div>



<div data-mb-exercise="oet-ac7cdc1d2ab36d93">

**习题 B.6（恒等分量与常值分量的导数判据）**：取 $A=\mathbb R^n$，设 $U\subseteq\mathbb R^n$ 为非空开凸集，$F:U\to\mathbb R^n$ 连续可微。令 $\phi_F$ 在 $U$ 上等于 $F$、在 $\mathcal X\setminus U$ 上取 $\bot$，并固定 $j\in I$。

**(i)** 证明下列三条等价：$F_j$ 在 $U$ 上为常值；$\nabla F_j(x)=0$ 对所有 $x\in U$ 成立；$j\in I_{\mathrm{const}}(\phi_F\mid U)$。

**(ii)** 固定 $x_0\in U$。证明下列三条等价：

1. $F_j(x)=x_j$ 对所有 $x\in U$ 成立；
2. $\nabla F_j(x)=e_j$ 对所有 $x\in U$ 成立，且 $F_j(x_0)=(x_0)_j$；
3. $j\in I_{\mathrm{id}}(\phi_F\mid U)$。

说明开集条件如何保证第 $j$ 个坐标在 $U$ 上不是常值，从而与正文的常值优先分划一致。

</div>



<div data-mb-exercise="oet-291a10c8f6ac11cb">

**习题 B.7（纤维中的方向与零化半径）**：取 $A=\mathbb R^2$ 和 $F(s,t)=(s,0)$，令 $\phi_F$ 在 $\mathbb R^2$ 上等于 $F$、在 $\bot$ 处取 $\bot$。对任意基点 $y=(y_1,y_2)$，求纤维 $F^{-1}(F(y))$ 及全族零化半径 $r^{\mathrm N}_{\phi_F,d_I,I}(y\mid\mathbb R^2)$，并说明为什么纤维包含一条直线仍不足以保证该半径为正。

</div>



<div data-mb-exercise="oet-ef39fb9c4b025f07">

**习题 B.8（逐步扰动与稀疏传播）**：设 $k\ge1$，$\mathbf M^{(m)}$（$1\le m\le k$）为逐条目有限的扩展非负矩阵。给定非负实向量

$$
e^{(m)}\in[0,+\infty)^n\quad(0\le m\le k),
\qquad r^{(m)}\in[0,+\infty)^n\quad(1\le m\le k),
$$

并假设逐分量满足

$$
e^{(m)}\le\mathbf M^{(m)}e^{(m-1)}+r^{(m)}
\qquad(1\le m\le k).
$$

**(i)** 证明递推展开

$$
e^{(k)}\le
\mathbf M^{(k)}\cdots\mathbf M^{(1)}e^{(0)}
+\sum_{m=1}^k
\mathbf M^{(k)}\cdots\mathbf M^{(m+1)}r^{(m)},
$$

其中 $m=k$ 时的空矩阵乘积取恒等矩阵；初始扰动 $e^{(0)}$ 不要求为零。

**(ii)** 对 $1\le m\le k$，令

$$
\alpha_m:=\|\mathbf M^{(m)}\|_{\infty\to\infty},
\qquad s_m:=s_{\mathrm{row}}(\mathbf M^{(m)}),
\qquad \lambda_m:=\max_{i,j\in I}[\mathbf M^{(m)}]_{ji}.
$$

证明

$$
\|e^{(k)}\|_\infty
\le\left(\prod_{t=1}^k\alpha_t\right)\|e^{(0)}\|_\infty
+\sum_{m=1}^k\left(\prod_{t=m+1}^k\alpha_t\right)\|r^{(m)}\|_\infty.
$$

再由 $\alpha_m\le s_m\lambda_m$ 推出

$$
\|e^{(k)}\|_\infty
\le\left(\prod_{t=1}^k s_t\lambda_t\right)\|e^{(0)}\|_\infty
+\sum_{m=1}^k\left(\prod_{t=m+1}^k s_t\lambda_t\right)\|r^{(m)}\|_\infty,
$$

其中空标量乘积取 $1$。

**(iii)** 设 $\phi_1,\ldots,\phi_k\in\mathcal X_{\mathrm{op}}$，$c_k=\phi_k\circ\cdots\circ\phi_1$。从非空集合 $U_1\subseteq\operatorname{dom}(\phi_1)$ 出发，递归令

$$
U_{m+1}=\phi_m(U_m)\subseteq\operatorname{dom}(\phi_{m+1})
\qquad(1\le m<k),
$$

并进一步假设 $\mathbf M^{(m)}\in\mathscr L(\phi_m)\big|_{U_m}$。对任意 $x,y\in U_1$，以两条实际轨迹的逐坐标差绝对值定义 $e^{(m)}$，取 $r^{(m)}=0$。验证题设递推，并证明

$$
d_I(c_k(x),c_k(y))
\le\left(\prod_{m=1}^k s_m\lambda_m\right)d_I(x,y).
$$

</div>
