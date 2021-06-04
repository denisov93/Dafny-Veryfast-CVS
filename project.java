/*@
//predicate Positive(unit a, int v; unit b) = v >= 0 &*& b == unit;

predicate QueueInv(Queue q; int n, int m) = 
	q.array |-> ?a
    &*& a != null
    &*& array_slice(a,0,a.length,?elems)
    &*& q.numelements |-> n
    &*& m == a.length
    &*& q.head |-> ?h
    &*& q.tail |-> ?t
    &*& 0 <= h &*& h < a.length
    &*& 0 <= t &*& t < a.length
    &*& (h==t? n==0 || n==a.length : true)
    &*& (h>t? n==h-t : true)
    &*& (h<t? n==h-t + a.length : true)
    ; 
@*/

//Queue based on a circular buffer.
class Queue {
    int[] array;
    int numelements;
    int head;
    int tail;
  
    //creates a new Queue with capacity max.
    Queue(int size)
    //@ requires size > 0;
    //@ ensures QueueInv(this,0,size);
    {
        array = new int[size];
        numelements = 0;
        head = 0;
        tail = 0;
    }
  
    //places the int v at the end of this Queue
    void enqueue(int v)
    //@ requires QueueInv(this,?n,?m) &*& n < m;
    //@ ensures QueueInv(this,n+1,m);
    {
        array[head++] = v;
        if(head == array.length) head = 0;
        numelements++;
    }
  
    //retrieves the element at the start of this Queue.
    int dequeue()
    //@ requires QueueInv(this,?n,?m) &*& n>0;
    //@ ensures QueueInv(this,n-1,m);
    {
        int v = array[tail++];
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