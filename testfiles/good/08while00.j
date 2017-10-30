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
ldc 3
dup
istore 0
pop
LBL0:
iconst_0
ifeq LBL1
iload 0
invokestatic CSupport/printInt(I)V
goto LBL0
LBL1:
return
nop
.end method
