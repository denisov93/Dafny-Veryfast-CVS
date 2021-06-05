import java.util.concurrent.locks.*;

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

/*@
predicate_ctor CQueueSharedState(CQueue c)(;) =
        c.q |-> ?q &*& q != null &*& QueueInv(q, _, _);

predicate_ctor CQueueSharedState_notempty(CQueue c)(;) =
        c.q |-> ?q &*& q != null &*& QueueInv(q, ?n, _) &*& n > 0;

predicate_ctor CQueueSharedState_notfull(CQueue c)(;) =
        c.q |-> ?q &*& q != null &*& QueueInv(q, ?n, ?m) &*& n < m;

predicate CQueueInv(CQueue c;) = 
        c.mon |-> ?l
        &*& l != null
        &*& l lck(l,l,CQueueSharedState(c));

        &*& c.notempty |-> ?c1
        &*& c1 != null
        &*& cond(c1, CQueueSharedState(c), CQueueSharedState_notempty(c))

        &*& c.notfull |-> ?c2
        &*& c2 != null
        &*& cond(c2, CQueueSharedState(c), CQueueSharedState_notfull(c))
@*/
  class CQueue {
    Queue q;
    ReentrantLock mon;
    Condition notempty;
    Condition notfull;

    CQueue(int size)
    //@ requires size > 0;
    //@ ensures CQueueInv(this);
    {
        q = new Queue(size);
        //@ close CQueueSharedState(this)();
        //@ close enter_lck(l, CQueueSharedState(this));
        mon = new ReentrantLock();
        //@ close set_cond(CQueueSharedState(this), CQueueSharedState_notempty(this));
        notempty = mon.newCondition();
        //@ close set_cond(CQueueSharedState(this), CQueueSharedState_notfull(this));
        notfull = mon.newCondition();
    }

      void enqueue(A v)
      //@ requires [?f]CQueueInv(this) &*& v != null &*& AInv(v);
      //@ ensures [f]CQueueInv(this);
      {
          mon.lock();
          if(!q.isFull()){
                notfull.await();
                //@ open CQueueSharedState_notfull(this)();
          }
          //@ open QueueInv(q,_,_);
          q.enqueue(v);
          notempty.signal();
          mon.unlock();
      }

      A dequeue()
      //@ requires [?f]CQueueInv(this);
      //@ ensures [f]CQueueInv(this);
      {
          mon.lock();
          if(!q.isEmpty()){
                notempty.await();
                //@ open CQueueSharedState_notempty(this)();
          }
          //@ open QueueInv(q,_,_)
          A v = q.dequeue();
          mon.unlock();
          notfull.signal();
          return v;
      }
  }

/*@
    predicate ProducerInv(Producer p;) = 
        p.q |-> ?q
        &*& q != null 
        &*& [_]CQueueInv(q)
        &*& p.id |-> ?v
        &*& v >= 0
@*/

//@predicate fraq(real f) = true;

class Producer implements Runnable{
    CQueue q;
    int id;

    //@ predicate pre() = ProducerInv(this);
    //@ predicate post() = emp;
    public Producer(CQueue q, int id)
    //@ requires q != null &*& frac(?f) &*& [f]CQueueInv(q) &*& id >= 0;
    //@ ensures ProducerInv(this);
    {
        this.q = q;
        this.id = id;
    }

    public void run(){
        //@ requires pre();
        //@ ensures post();
        while(true)
        //@ invariant ProducerInv(this);
        {
            q.enqueue(new A(id));
        }
    }
}

class Consumer{

}

class ProducerConsumer {

    public static void main(String []args)
    //@ requires true;
    //@ ensures true;
    {
        CQueue q = new CQueue(10);
        //@ assert CQueueInv(q);
        //@ close frac(1);
        for( int i = 0; i < 10; i++ )
        //@ invariant 0 <= i &*& i <= 10 &*& frac(?f) &*& [f]CQueueInv(q);
        {
            //@open fraq(f);
            //@close fraq(f/2);
            new Thread(new Producer(q,i)).start();
            //@close fraq(f/2);
            new Thread(new Consumer(q)).start();
        }
    }
}