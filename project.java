import java.util.concurrent.locks.*;

/*@
predicate Valid(unit a, A o; unit b) = o != null &*& AInv(o) &*& b == unit;

predicate AInv(A o;) = o.a |-> ?v &*& v >= 0;

predicate QueueInv(Queue q; int h, int t, int m) = 
	q.input |-> ?a
    &*& q.output |-> ?b
    &*& q.in_n |-> h
    &*& q.out_n |-> t
    &*& a != null
    &*& b != null
    //pode escrever e ler na pos de vetor 
    &*& m == a.length
    &*& a.length == b.length
    &*& 0 <= h &*& h <= m
    &*& 0 <= t &*& t <= m
    &*& h+t <= m
    &*& m > 0
    
    &*& array_slice_deep(a, 0, h, Valid, unit, ?in, _)
    &*& array_slice(a, h, m, ?out2)
    
    //&*& array_slice(b,0,b.length,?out3)
    &*& array_slice_deep(b, 0, t, Valid, unit, ?in2, _)
    &*& array_slice(b, t, m, ?out4)

    ; 
    
predicate LoopInv(Queue q; int h, int t, int m) = 
	q.input |-> ?a
    &*& q.output |-> ?b
    &*& q.in_n |-> h
    &*& q.out_n |-> t
    &*& a != null
    &*& b != null
    //pode escrever e ler na pos de vetor 
    &*& m == a.length
    &*& a.length == b.length
    &*& 0 <= h &*& h <= m
    &*& 0 <= t &*& t <= m
    &*& h+t <= m
    &*& m > 0
    
    &*& array_slice_deep(a, 0, h, Valid, unit, ?in, _)
    &*& array_slice(a, h, m, ?out2)
    
    //&*& array_slice(b,0,b.length,?out3)
    &*& array_slice_deep(b, 0, t, Valid, unit, ?in2, _)
    &*& array_slice(b, t, m, ?out4)

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


class Queue {
    A[] input;
    A[] output;
    int in_n;
    int out_n;
  
    //creates a new Queue with capacity max.
    Queue(int size)
    //@ requires size > 0;
    //@ ensures QueueInv(this,0,0,size);
    {
        input = new A[size];
        output = new A[size];
        in_n = 0;
        out_n = 0;
    }
  
    //places the int v at the end of this Queue
    void enqueue(A v)
    //@ requires QueueInv(this,?h,?t,?m) &*& v!=null &*& AInv(v) &*& h + t < m;
    //@ ensures (h<m ? QueueInv(this,h+1,t,m) : QueueInv(this,h,t,m) );
    {
        
        if(in_n < input.length){
        
        input[in_n] = v;
        in_n++;
        
        } 
    }
  
    //retrieves the element at the start of this Queue.
    A dequeue()
    //@ requires QueueInv(this,?h,?t,?m) &*& h+t > 0;
    //@ ensures (t == 0 ? QueueInv(this,0,h-1,m) : QueueInv(this,h,t-1,m)) &*& result != null &*& AInv(result);
    {
        
        if(out_n == 0){
            flush();
        }
        
        out_n -= 1;
        if(out_n >= 0){
        return output[out_n];
	}else{
	
	return null;
	}        
        

    }
    
    //returns true if this Queue has reached its capacity.
    boolean isFull()
    //@ requires QueueInv(this,?h,?t,?m);
    //@ ensures QueueInv(this,h,t,m) &*& result == (h+t==m);
    {
        return in_n + out_n == input.length;
    }
    
    //returns true if this Queue has no elements.
    boolean isEmpty()
    //@ requires QueueInv(this,?h,?t,?m);
    //@ ensures QueueInv(this,h,t,m) &*& result == (h+t==0);
    {
        return in_n + out_n == 0;
    }
  
    void flush()
    //@ requires QueueInv(this,?h,?t,?m) &*& t == 0 &*& h > 0;
    //@ ensures QueueInv(this,0,h,m);
    {
    	//@ close LoopInv(this,_,_,m);
        while (in_n > 0)
        ///@ invariant QueueInv(this,?h1,?t1,?m1);
        //@ invariant LoopInv(this,?h1,?t1, m) &*& h1+t1 == h;
        {
            output[out_n] = input[in_n-1];
            in_n-=1;
            out_n+=1;
        }
    }
  }

/*@
predicate_ctor CQueueSharedState(CQueue c)(;) =
        c.q |-> ?q &*& q != null &*& QueueInv(q, _, _, _);

predicate_ctor CQueueSharedState_notempty(CQueue c)(;) =
        c.q |-> ?q &*& q != null &*& QueueInv(q, ?h, ?t, _) &*& h + t > 0;

predicate_ctor CQueueSharedState_notfull(CQueue c)(;) =
        c.q |-> ?q &*& q != null &*& QueueInv(q, ?h, ?t, ?m) &*& h + t < m;

predicate CQueueInv(CQueue c;) = 
            c.mon |-> ?l
        &*& l != null
        &*& lck(l, 1, CQueueSharedState(c))

        &*& c.notempty |-> ?c1
        &*& c1 != null
        &*& cond(c1, CQueueSharedState(c), CQueueSharedState_notempty(c))

        &*& c.notfull |-> ?c2
        &*& c2 != null
        &*& cond(c2, CQueueSharedState(c), CQueueSharedState_notfull(c))
        ;
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
        //@ close enter_lck(1, CQueueSharedState(this));
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
          if(q.isFull()){
                try {
					notfull.await();
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
                //@ open CQueueSharedState_notfull(this)();
          }
          //@ open QueueInv(q,?h,_,_);
          q.enqueue(v);
          notempty.signal();
          mon.unlock();
      }

      A dequeue()
      //@ requires [?f]CQueueInv(this);
      //@ ensures [f]CQueueInv(this);
      {
          mon.lock();
          if( q.isEmpty()){
                try {
					notempty.await();
				} catch (InterruptedException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
                //@ open CQueueSharedState_notempty(this)();
          }
          //@ open QueueInv(q,_,_,_);
          A v = q.dequeue();
          notfull.signal();
          mon.unlock();
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
        ;
@*/

/*@
    predicate ConsumerInv(Consumer c;) = 
            c.q |-> ?q
        &*& q != null 
        &*& [_]CQueueInv(q)
        &*& c.id |-> ?v
        &*& v >= 0
        ;
@*/

//@predicate frac(real f) = true;



class Producer implements Runnable{
    CQueue q;
    int id;

    //@ predicate pre() = ProducerInv(this) &*& [_]System_out(?z) &*& z != null ;
    //@ predicate post() = emp;
    public Producer(CQueue q, int id)
    //@ requires q != null &*& frac(?f) &*& [f]CQueueInv(q) &*& id >= 0;
    //@ ensures ProducerInv(this);
    {
        this.q = q;
        this.id = id;
    }

    public void run()
        //@ requires pre();
        //@ ensures post();
    {
    
    //System.out.println("hh");
        while(true)
        //@ invariant ProducerInv(this) &*& [?f]System_out(?z) &*& z != null;
        {
            A a = new A(id);
            q.enqueue(a);
            ///@ open frac(f);
            //@ close frac(f/2);
            System.out.println("Enqeued: "+String.valueOf(id));//String.valueOf(id));
            //@ close frac(f/2);
            //	Thread.sleep(100);
        }
    }
}

class Consumer implements Runnable{
    CQueue q;
    int id;

    //@ predicate pre() = ConsumerInv(this) &*& [_]System_out(?z) &*& z != null ;
    //@ predicate post() = emp;
    public Consumer(CQueue q, int id)
    //@ requires q != null &*& frac(?f) &*& [f]CQueueInv(q) &*& id >= 0;
    //@ ensures ConsumerInv(this);
    {
        this.q = q;
        this.id = id;
    }

    public void run()
        //@ requires pre();
        //@ ensures post();
    {
        while(true)
        //@ invariant ConsumerInv(this) &*& [?f]System_out(?z) &*& z != null;
        {
            A a = q.dequeue();
			 //@ close frac(f/2);
			 System.out.println("Enqeued: "+String.valueOf(id));//String.valueOf(id));
			 //@ close frac(f/2);
			//Thread.sleep(100);
        }
    }
}

class ProducerConsumer {

    public static void main(String []args)
    //@ requires System_out(?o) &*& o != null;
    //@ ensures true;
    {
        //System.out.println("...");
        CQueue q = new CQueue(100);
        //@ assert CQueueInv(q);
        //@ close frac(1);
        for( int i = 0; i < 100; i++ )
        //@ invariant 0 <= i &*& i <= 100 &*& frac(?f) &*& [f]CQueueInv(q) &*& [_]System_out(?z) &*& z != null;
        {
            System.out.println("...");
            //@ open frac(f);
            //@ close frac(f/2);
            new Thread(new Producer(q,i)).start();
            //@ close frac(f/4);
            new Thread(new Consumer(q,1000+i)).start();
            //@ close frac(f/4);
        }
    }

}