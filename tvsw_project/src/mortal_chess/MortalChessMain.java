package mortal_chess;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

public class MortalChessMain {
	
	public static void main(String[] args) throws IOException {
		
		BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
		Tavolo tavolo = Tavolo.getTavolo();
		Partita p = new Partita(reader, tavolo);
		p.gioca();
		
	}

}
