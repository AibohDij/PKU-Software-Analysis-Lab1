package test;

import benchmark.internal.Benchmark;
import benchmark.objects.B;

public class Hello {

  public static void main(String[] args) {
    Benchmark.alloc(3);
    B b = new B();
    Benchmark.alloc(4);
    B a = new A();
    Benchmark.test(7, b);
    Benchmark.test(8, a);
  }
}
/*
Answer:
  7 : 3
*/
