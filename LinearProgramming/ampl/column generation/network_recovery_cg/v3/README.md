# 这里的pricing的模型有问题

中间看上去奇奇怪怪，竟然还有一些自发的loop?

## 把loop去掉了

但是现在的问题是
- pricing1.mod是现在最新的model，但是它得到的最有解并不是最优的

- 可以用原来的model来检查是否有一个新的可以使得它增加。

## 重要文件

- nc_cg4-int.mod: 这个文件只有binary的variable和constraint，其他一概没有，目的是运行完column generation之后来找
一个最优解

- nc_cg4-original.mod: 这个文件里面有所有的定义以及binary类型的variable和constraint

- nc_cg4.mod: 这个文件里面有做过relaxation的变量和所有的定义