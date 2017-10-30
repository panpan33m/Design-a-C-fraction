.class public C
.super java/lang/Object

.method public <init>()V
  aload_0
  invokenonvirtual java/lang/Object/<init>()V
  return
.end method

.method public static main([Ljava/lang/String;)V
.limit locals 1000
.limit stack 1000
invokestatic CSupport/readInt()I
dup
istore 0
pop
iload 0
ldc 2
idiv
dup
istore 2
pop
LBL0:
ldc 1
iload 2
ldc 1
if_icmpgt LBL2
pop
ldc 0
LBL2:
ifeq LBL1
ldc 1
iload 2
iload 0
iload 2
idiv
imul
iload 0
if_icmpeq LBL5
pop
ldc 0
LBL5:
ifeq LBL4
iload 2
invokestatic CSupport/printInt(I)V
goto LBL3
LBL4:
LBL3:
iload 2
iinc 2 -1
pop
goto LBL0
LBL1:
return
nop
.end method
