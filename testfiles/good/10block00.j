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
ldc 6
dup
istore 0
pop
iload 0
ldc 7
iadd
dup
istore 2
pop
iload 2
invokestatic CSupport/printInt(I)V
ldc 4
dup
istore 4
pop
iload 4
invokestatic CSupport/printInt(I)V
iload 4
dup
istore 0
pop
iload 0
invokestatic CSupport/printInt(I)V
iload 0
invokestatic CSupport/printInt(I)V
iload 2
invokestatic CSupport/printInt(I)V
return
nop
.end method
