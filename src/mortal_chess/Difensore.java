package mortal_chess;

public class Difensore extends Pedina {

	private /*@ spec_public @*/ int puntiDifesa;
	
	/*@ requires g == 'X' || g == 'O';
	  @ requires r >= 1 && r <= 8;
	  @ requires c >= 'A' && c <= 'H';
	  @ requires p >= 1;
	  @ ensures this.giocatore == g;
	  @ ensures this.cella.getPrimo() == r;
	  @ ensures this.cella.getSecondo() == c;
	  @ ensures this.puntiDifesa == p;
	  @*/
	public Difensore(char g, int r, char c, int p) {
		super(g, r, c);
		puntiDifesa = p;
	}
	
	/*@ requires g == 'X' || g == 'O';
	  @ requires r >= 1 && r <= 8;
	  @ requires c >= 'A' && c <= 'H';
	  @ ensures this.giocatore == g;
	  @ ensures this.cella.getPrimo() == r;
	  @ ensures this.cella.getSecondo() == c;
	  @ ensures this.puntiDifesa == 1;
	  @*/
	public Difensore(char g, int r, char c) {
		this(g, r, c, 1);
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
	
	//@ also ensures \result == false;
	@Override
	public boolean isAttaccante() {
		return false;
	}

	//@ also ensures \result == true;
	@Override
	public boolean isDifensore() {
		return true;
	}
	
	/*@ also
	  @ requires p != null;
	  @ ensures p instanceof AttaccanteDifensore ==> (\result instanceof AttaccanteDifensore &&
	  @ 											((AttaccanteDifensore)\result).getPuntiAttacco() == ((AttaccanteDifensore)p).getPuntiAttacco() &&
	  @ 											((AttaccanteDifensore)\result).getPuntiDifesa() == this.getPuntiDifesa() + ((AttaccanteDifensore)p).getPuntiDifesa());
	  @ ensures p instanceof Difensore ==> (\result instanceof Difensore &&
	  @ 									((Difensore)\result).getPuntiDifesa() == this.getPuntiDifesa() + ((Difensore)p).getPuntiDifesa());
	  @ ensures p instanceof Attaccante ==> (\result instanceof AttaccanteDifensore &&
	  @ 									((AttaccanteDifensore)\result).getPuntiAttacco() == ((Attaccante)p).getPuntiAttacco() &&
	  @ 									((AttaccanteDifensore)\result).getPuntiDifesa() == this.getPuntiDifesa());
	  @ ensures (\result).getGiocatore() == this.getGiocatore() && \result.getRiga() == this.getRiga() && \result.getColonna() == this.getColonna();
	  @*/
	@Override
	public Pedina unisci(Pedina p) {
		Pedina result;
		if (p.isAttaccanteDifensore()) {
			AttaccanteDifensore t = (AttaccanteDifensore) p;
			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), t.getPuntiAttacco(), getPuntiDifesa() + t.getPuntiDifesa());
		}
		else if (p.isDifensore()) {
			Difensore t = (Difensore) p;
			result = new Difensore(getGiocatore(), getRiga(), getColonna(), getPuntiDifesa() + t.getPuntiDifesa());
		}
		else {
			Attaccante t = (Attaccante) p;
			result = new AttaccanteDifensore(getGiocatore(), getRiga(), getColonna(), t.getPuntiAttacco(), getPuntiDifesa());
		}
		return result;
	}
	
	/*@ also
	  @ requires p >= 1;
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
		return super.toString() + " (D) - Punti Difesa: " + getPuntiDifesa();
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!(obj instanceof Difensore))
			return false;
		Difensore d = (Difensore) obj;
		return this.getGiocatore() == d.getGiocatore() &&
				this.getRiga() == d.getRiga() &&
				this.getColonna() == d.getColonna() &&
				this.getPuntiDifesa() == d.getPuntiDifesa();
	}
	
}
