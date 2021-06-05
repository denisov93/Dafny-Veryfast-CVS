/*@
predicate Valid(unit a, A o; unit b) = o != null &*& AInv(o) &*& b == unit;

predicate AInv(A o;) = o.a |-> ?v &*& v >= 0;

predicate QueueInv(Queue q; int n, int m) = 
	q.array |-> ?a
    &*& a != null
    &*& q.numelements |-> n
    &*& m == a.length
    &*& q.head |-> ?h
    &*& q.tail |-> ?t
    &*& 0 <= h &*& h < a.length
    &*& 0 <= t &*& t < a.length
    &*& (h==t? n==0 || n==a.length : true)
    &*& (h>t? n==h-t : true)
    &*& (h<t? n==h-t + a.length : true)
  
    &*& (h>t || h==t && n==0 ?
    	    array_slice(a,0,t,?out1)
    	&*& array_slice_deep(a,t,h,Valid, unit, ?in, _)
    	&*& array_slice(a, h, a.length, ?out2)
    	:
    	    array_slice_deep(a,0,h,Valid, unit,?in1,_)
    	&*& array_slice(a,h,t,?out)
    	&*& array_slice_deep(a,t,a.length,Valid, unit,?in2,_)
        )
    ; 
@*/

class A{
    int a;
    
    public A(int a)
    //@ requires a >= 0;
    //@ ensures AInv(this);
    {
	    this.a = a;
    }
}


//Queue based on a circular buffer.
class Queue {
    A[] array;
    int numelements;
    int head;
    int tail;
  
    //creates a new Queue with capacity max.
    Queue(int size)
    //@ requires size > 0;
    //@ ensures QueueInv(this,0,size);
    {
        array = new A[size];
        numelements = 0;
        head = 0;
        tail = 0;
    }
  
    //places the int v at the end of this Queue
    void enqueue(A v)
    //@ requires QueueInv(this,?n,?m) &*& v!=null &*& AInv(v) &*& n < m;
    //@ ensures QueueInv(this,n+1,m);
    {
        array[head++] = v;
        if(head == array.length) head = 0;
        numelements++;
    }
  
    //retrieves the element at the start of this Queue.
    A dequeue()
    //@ requires QueueInv(this,?n,?m) &*& n>0;
    //@ ensures QueueInv(this,n-1,m);
    {
        A v = array[tail++];
        array[tail-1] = null;
        numelements--;
        if(tail==array.length) tail=0;
        return v;
    }
    
    //returns true if this Queue has reached its capacity.
    boolean isFull()
    //@ requires QueueInv(this,?n,?m);
    //@ ensures QueueInv(this,n,m) &*& result == (n==m);
    {
        return numelements== array.length;
    }
    
    //returns true if this Queue has no elements.
    boolean isEmpty()
    //@ requires QueueInv(this,?n,?m);
    //@ ensures QueueInv(this,n,m) &*& result == (n==0);
    {
        return numelements == 0;
    }
  
  }