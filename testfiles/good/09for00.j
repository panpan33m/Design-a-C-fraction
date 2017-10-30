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
ldc 5
dup
istore 0
pop
ldc 4
dup
istore 2
pop
iload 2
istore 4
LBL1:
ldc 1
iload 4
ldc 0
if_icmpgt LBL2
pop
ldc 0
LBL2:
ifeq LBL0
iload 0
iload 4
iadd
dup
istore 0
pop
iload 0
invokestatic CSupport/printInt(I)V
iinc 4 -1
iload 4
pop
goto LBL1
LBL0:
iload 2
invokestatic CSupport/printInt(I)V
iload 0
invokestatic CSupport/printInt(I)V
return
nop
.end method
