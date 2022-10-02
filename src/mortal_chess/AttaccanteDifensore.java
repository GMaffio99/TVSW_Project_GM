package mortal_chess;

public class AttaccanteDifensore extends Pedina {

	private /*@ spec_public @*/ int puntiAttacco;
	private /*@ spec_public @*/ int puntiDifesa;
	
	/*@ requires g == 'X' || g == 'O';
	  @ requires r >= 1 && r <= 8;
	  @ requires c >= 'A' && c <= 'H';
	  @ requires a >= 1 && d >= 1;
	  @ ensures this.giocatore == g;
	  @ ensures this.cella.getPrimo() == r;
	  @ ensures this.cella.getSecondo() == c;
	  @ ensures this.puntiAttacco == a;
	  @ ensures this.puntiDifesa == d;
	  @*/
	public AttaccanteDifensore(char g, int r, char c, int a, int d) {
		super(g, r, c);
		puntiAttacco = a;
		puntiDifesa = d;
	}
		
	//@ ensures \result == this.puntiAttacco;
	//@ pure
	public int getPuntiAttacco() {
		return puntiAttacco;
	}
	
	//@ requires p >= 1;
	//@ ensures this.puntiAttacco == p;
	public void setPuntiAttacco(int p) {
		puntiAttacco = p;
	}
	
	//@ ensures \result == this.puntiDifesa;
	//@ pure
	public int getPuntiDifesa() {
		return puntiDifesa;
	}
	
	//@ requires p >= 1;
	//@ ensures this.puntiDifesa == p;
	public void setPuntiDifesa(int p) {
		puntiDifesa = p;
	}
	
	//@ also ensures \result == true;
	@Override
	public boolean isAttaccante() {
		return true;
	}

	//@ also ensures \result == true;
	@Override
	public boolean isDifensore() {
		return true;
	}
	
	/*@ also
	  @ requires p != null;
	  @ ensures p instanceof AttaccanteDifensore ==> (\result instanceof AttaccanteDifensore &&
	  @ 											((AttaccanteDifensore)\result).getPuntiAttacco() == this.getPuntiAttacco() + ((AttaccanteDifensore)p).getPuntiAttacco() &&
	  @ 											((AttaccanteDifensore)\result).getPuntiDifesa() == this.getPuntiDifesa() + ((AttaccanteDifensore)p).getPuntiDifesa());
	  @ ensures p instanceof Difensore ==> (\result instanceof AttaccanteDifensore &&
	  @ 									((AttaccanteDifensore)\result).getPuntiAttacco() == this.getPuntiAttacco() &&
	  @										((AttaccanteDifensore)\result).getPuntiDifesa() == this.getPuntiDifesa() + ((Difensore)p).getPuntiDifesa());
	  @ ensures p instanceof Attaccante ==> (\result instanceof AttaccanteDifensore &&
	  @ 									((AttaccanteDifensore)\result).getPuntiAttacco() == this.getPuntiAttacco() + ((Attaccante)p).getPuntiAttacco() &&
	  @ 									((AttaccanteDifensore)\result).getPuntiDifesa() == this.getPuntiDifesa());
	  @ ensures (\result).getGiocatore() == this.getGiocatore() && \result.getRiga() == this.getRiga() && \result.getColonna() == this.getColonna();
	  @*/
	@Override
	public Pedina unisci(Pedina p) {
		Pedina result;
		if (p.isAttaccanteDifensore()) {
			AttaccanteDifensore t = (AttaccanteDifensore) p;
			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), getPuntiAttacco() + t.getPuntiAttacco(), getPuntiDifesa() + t.getPuntiDifesa());
		}
		else if (p.isDifensore()) {
			Difensore t = (Difensore) p;
			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), getPuntiAttacco(), getPuntiDifesa() + t.getPuntiDifesa());
		}
		else {
			Attaccante t = (Attaccante) p;
			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), getPuntiAttacco() + t.getPuntiAttacco(), getPuntiDifesa());
		}
		return result;
	}
	
	//@ ensures this.puntiAttacco == \old(this.puntiAttacco) - 1;
	//@ ensures this.puntiAttacco <= 0 <==> \result == true;
	//@ ensures this.puntiAttacco > 0 <==> \result == false;
	public boolean attacca() {
		setPuntiAttacco(getPuntiAttacco() - 1);
		return getPuntiAttacco() <= 0;
	}

	/*@ also
	  @requires p >= 1;
	  @ ensures this.puntiDifesa == \old(this.puntiDifesa) - p;
	  @ ensures this.puntiDifesa <= 0 <==> \result == true;
	  @ ensures this.puntiDifesa > 0 <==> \result == false;
	  @*/
	@Override
	public boolean vieneAttaccata(int p) {
		setPuntiDifesa(getPuntiDifesa() - p);
		return getPuntiDifesa() <= 0;
	}

	
	@Override
	public String toString() {
		return super.toString() + " (AD) - Punti Attacco: " + getPuntiAttacco() + " - Punti Difesa: " + getPuntiDifesa();
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!(obj instanceof AttaccanteDifensore))
			return false;
		AttaccanteDifensore ad = (AttaccanteDifensore) obj;
		return this.getGiocatore() == ad.getGiocatore() &&
				this.getRiga() == ad.getRiga() &&
				this.getColonna() == ad.getColonna() &&
				this.getPuntiAttacco() == ad.getPuntiAttacco() &&
				this.getPuntiDifesa() == ad.getPuntiDifesa();
	}
	
}
