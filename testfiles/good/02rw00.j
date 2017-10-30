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
invokestatic CSupport/printInt(I)V
invokestatic CSupport/readDouble()D
dup2
dstore 2
pop2
dload 2
invokestatic CSupport/printDouble(D)V
invokestatic CSupport/readBool()Z
dup
istore 5
pop
iload 5
invokestatic CSupport/printBool(Z)V
