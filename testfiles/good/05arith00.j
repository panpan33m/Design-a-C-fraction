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
ldc 7
dup
istore 0
ldc 4
dup
istore 2
pop
pop
ldc2_w 3.0
dup2
dstore 4
ldc2_w 4.0
dup2
dstore 7
pop2
pop2
iload 0
iload 2
iadd
invokestatic CSupport/printInt(I)V
iload 0
iload 2
isub
invokestatic CSupport/printInt(I)V
iload 0
iload 2
imul
invokestatic CSupport/printInt(I)V
iload 0
iload 2
idiv
invokestatic CSupport/printInt(I)V
iload 0
iload 2
irem
invokestatic CSupport/printInt(I)V
dload 4
dload 7
dadd
invokestatic CSupport/printDouble(D)V
dload 4
dload 7
dsub
invokestatic CSupport/printDouble(D)V
dload 4
dload 7
dmul
invokestatic CSupport/printDouble(D)V
dload 4
dload 7
ddiv
invokestatic CSupport/printDouble(D)V
return
nop
.end method
