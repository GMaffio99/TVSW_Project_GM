package mortal_chess;

import java.io.BufferedReader;
import java.io.IOException;

import static mortal_chess.TavoloUtils.*;

public class Partita {
	
	private /*@ spec_public @*/ final BufferedReader reader;
	private /*@ spec_public @*/ final Tavolo tavolo;
	
	/*@ requires reader != null && tavolo != null;
	  @ ensures this.reader == reader && this.tavolo == tavolo;
	  @*/
	public Partita(final BufferedReader reader, final Tavolo tavolo) {
		this.reader = reader;
		this.tavolo = tavolo;
	}
	

	/*@ requires intestazione != null &&
	  @ 		(intestazione.equals(new String("[X]")) || intestazione.equals(new String("[O]")));
	  @ ensures \result.length() == 2 &&
	  @ 		\result.charAt(0) >= 'A' && \result.charAt(0) <= 'H' &&
	  @ 		\result.charAt(1) >= '1' && \result.charAt(1) <= '8';
	  @*/
	public String selezioneCella(String intestazione) throws IOException {
		String cella;
		boolean esito;
		do {
			System.out.println(intestazione);
			cella = reader.readLine();
			if (cella.length() != 2)
				esito = true;
			else {
				char colonna = cella.toUpperCase().charAt(0);
				char riga = cella.charAt(1);
				esito = colonna != 'A' && colonna != 'B' && colonna != 'C' && colonna != 'D' && colonna != 'E' && colonna != 'F' && colonna != 'G' && colonna != 'H' ||
						riga != '1' && riga != '2' && riga != '3' && riga != '4' && riga != '5' && riga != '6' && riga != '7' && riga != '8';
			}
			if (esito)
				System.out.println(intestazione.substring(0, 3) + " SCELTA NON VALIDA");
		} while (esito);
		return cella;
	}

	
	public void impostaPunti() throws IOException {
		
		String entry;
		int punti = 0;
		
		do {
			System.out.println("~~~ SCEGLIETE I PUNTI VITA DEI GIOCATORI: ~~~");
			entry = reader.readLine();
			if (!isInteger(entry))
				System.out.println("~~~ SCELTA NON VALIDA, INSERITE UN NUMERO INTERO ~~~");
			else {
				punti = Integer.parseInt(entry);
				if (punti <= 0)
					System.out.println("~~~ SCELTA NON VALIDA, INSERITE UN NUMERO POSITIVO ~~~");
			}
		} while (punti <= 0);
		
		tavolo.setPunti(punti);
		
	}
	
	/*@ requires giocatore == 'X' || giocatore == 'O';
	  @ requires intestazione != null &&
	  @ 		(intestazione.equals(new String("[X]")) || intestazione.equals(new String("[O]")));
	  @ ensures \result >= '1' && \result <= '5';
	  @*/
	public char selezionaMossa(char giocatore, String intestazione) throws IOException {
		
		String entry;
		char mossa;
		
		do {

			System.out.println(intestazione + " SCEGLI UNA MOSSA DA ESEGUIRE:");
			System.out.println(intestazione + " 1 - Piazzare una pedina");
			System.out.println(intestazione + " 2 - Muovere una pedina");
			System.out.println(intestazione + " 3 - Unire due pedine");
			System.out.println(intestazione + " 4 - Attaccare una pedina");
			System.out.println(intestazione + " 5 - Attaccare l'avversario");
			entry = reader.readLine();

			mossa = entry.length() == 1 ? entry.charAt(0) : '0';

			if (mossa != '1' && mossa != '2' && mossa != '3' && mossa != '4' && mossa != '5')
				System.out.println(intestazione + " SCELTA NON VALIDA - Inserire un carattere tra quelli proposti");

		} while (!tavolo.mossaEseguibile(mossa, giocatore));
		
		return mossa;
		
	}

	/*@ requires giocatore == 'X' || giocatore == 'O';
	  @ requires intestazione != null &&
	  @ 		(intestazione.equals(new String("[X]")) || intestazione.equals(new String("[O]")));
	  @*/
	public void posizionarePedina(char giocatore, String intestazione) throws IOException {
		
		String entry;
		String cella;
		int esito;
		char tipologia;

		do {

			System.out.println(intestazione + " SELEZIONA LA TIPOLOGIA DI PEDINA DA PIAZZARE ([A] ATTACCANTE, [D] DIFENSORE):");
			entry = reader.readLine();
			tipologia = entry.length() == 1 ? entry.toUpperCase().charAt(0) : '0';

			if (tipologia != 'A' && tipologia != 'D')
				System.out.println(intestazione + " SCELTA NON VALIDA - Inserire un carattere tra quelli proposti");

		} while (tipologia != 'A' && tipologia != 'D');

		char colonna;
		char riga;
		char col = giocatore == 'X' ? 'A' : 'H';

		do {
			cella = selezioneCella(intestazione + " SELEZIONA LA CELLA SU CUI POSIZIONARE LA PEDINA (" + col + "1-" + col + "8)");
			colonna = cella.toUpperCase().charAt(0);
			riga = cella.charAt(1);
			esito = colonna == col ? 0 : 1;
			if (esito != 0)
				System.out.println(intestazione + " LA CELLA DEVE ESSERE POSIZIONATA SULLA COLONNA " + col);
			else {
				esito = tavolo.cellaOccupata(riga, colonna) ? 1 : 0;
				if (esito != 0)
					System.out.println(intestazione + " LA CELLA " + colonna + riga + " E' GIA' OCCUPATA, SELEZIONA UN'ALTRA CELLA");
			}
		} while (esito != 0);

		tavolo.posizionaPedina(giocatore, tipologia, riga, colonna);
		
	}
	
	/*@ requires giocatore == 'X' || giocatore == 'O';
	  @ requires intestazione != null &&
	  @ 		(intestazione.equals(new String("[X]")) || intestazione.equals(new String("[O]")));
	  @*/
	public void muoverePedina(char giocatore, String intestazione) throws IOException {
		
		String cella;
		int esito;
		char riga1;
		char colonna1;

		do {
			cella = selezioneCella(intestazione + " SELEZIONA LA CELLA DELLA PEDINA DA MUOVERE (A1-H8):");
			colonna1 = cella.toUpperCase().charAt(0);
			riga1 = cella.charAt(1);
			esito = tavolo.pedinaMovibile(giocatore, riga1, colonna1);
			if (esito == -1) {
				System.out.println(intestazione + " LA PEDINA NELLA CELLA " + colonna1 + riga1 + " APPARTIENE ALL'AVVERSARIO, SELEZIONA UN'ALTRA PEDINA");
			} else if (esito == 1) {
				System.out.println(intestazione + " LA PEDINA NELLA CELLA " + colonna1 + riga1 + " NON PUO' ESSERE MOSSA, SELEZIONA UN'ALTRA PEDINA");
			} else if (esito == 2) {
				System.out.println(intestazione + " NELLA CELLA " + colonna1 + riga1 + " NON E' PRESENTE UNA PEDINA, SELEZIONA UN'ALTRA CELLA");
			}
		} while (esito != 0);

		char riga2;
		char colonna2;

		do {
			cella = selezioneCella(intestazione + " SELEZIONA LA CELLA DI DESTINAZIONE DELLA PEDINA (A1-H8):");
			colonna2 = cella.toUpperCase().charAt(0);
			riga2 = cella.charAt(1);
			esito = tavolo.cellaRaggiungibile(riga1, colonna1, riga2, colonna2);
			if (esito == -1) {
				System.out.println(intestazione + " LA CELLA " + colonna2 + riga2 + " NON E' RAGGIUNGIBILE DALLA PEDINA SELEZIONATA, SELEZIONA UN'ALTRA CELLA");
			} else if (esito == 1) {
				System.out.println(intestazione + " LA CELLA " + colonna2 + riga2 + " E' GIA' OCCUPATA, SELEZIONA UN'ALTRA CELLA");
			}
		} while (esito != 0);

		tavolo.muoviPedina(riga1, colonna1, riga2, colonna2);
		
	}
	
	/*@ requires giocatore == 'X' || giocatore == 'O';
	  @ requires intestazione != null &&
	  @ 		(intestazione.equals(new String("[X]")) || intestazione.equals(new String("[O]")));
	  @*/
	public void unirePedine(char giocatore, String intestazione) throws IOException {
		
		String cella;
		int esito;
		char riga1;
		char colonna1;

		do {
			cella = selezioneCella(intestazione + " SELEZIONA LA CELLA DELLA PRIMA PEDINA DA UNIRE (A1-H8):");
			colonna1 = cella.toUpperCase().charAt(0);
			riga1 = cella.charAt(1);
			esito = tavolo.pedinaUnibile(giocatore, riga1, colonna1);
			if (esito == -1) {
				System.out.println(intestazione + " LA PEDINA NELLA CELLA " + colonna1 + riga1 + " APPARTIENE ALL'AVVERSARIO, SELEZIONA UN'ALTRA PEDINA");
			} else if (esito == 1) {
				System.out.println(intestazione + " LA PEDINA NELLA CELLA " + colonna1 + riga1 + " NON PUO' ESSERE UNITA, SELEZIONA UN'ALTRA PEDINA");
			} else if (esito == 2) {
				System.out.println(intestazione + " NELLA CELLA " + colonna1 + riga1 + " NON E' PRESENTE UNA PEDINA, SELEZIONA UN'ALTRA CELLA");
			}
		} while (esito != 0);

		char riga2;
		char colonna2;

		do {
			cella = selezioneCella(intestazione + " SELEZIONA LA CELLA DELLA SECONDA PEDINA DA UNIRE (A1-H8):");
			colonna2 = cella.toUpperCase().charAt(0);
			riga2 = cella.charAt(1);
			esito = tavolo.pedineUnibili(giocatore, riga1, colonna1, riga2, colonna2);
			if (esito == -1) {
				System.out.println(intestazione + " LA PEDINA NELLA CELLA " + colonna2 + riga2 + " APPARTIENE ALL'AVVERSARIO, SELEZIONA UN'ALTRA PEDINA");
			} else if (esito == 1) {
				System.out.println(intestazione + " LE PEDINE NELLE CELLE " + colonna1 + riga1 + " E " + colonna2 + riga2 + " NON POSSONO ESSERE UNITE, SELEZIONA UN'ALTRA PEDINA");
			} else if (esito == 2) {
				System.out.println(intestazione + " NELLA CELLA " + colonna2 + riga2 + " NON E' PRESENTE UNA PEDINA, SELEZIONA UN'ALTRA CELLA");
			}
		} while (esito != 0);

		tavolo.unisciPedine(riga1, colonna1, riga2, colonna2);
		
	}
	
	/*@ requires giocatore == 'X' || giocatore == 'O';
	  @ requires intestazione != null &&
	  @ 		(intestazione.equals(new String("[X]")) || intestazione.equals(new String("[O]")));
	  @*/
	public void attaccarePedina(char giocatore, String intestazione) throws IOException {
		
		String cella;
		int esito;
		char riga1;
		char colonna1;

		do {
			cella = selezioneCella(intestazione + " SELEZIONA LA CELLA DELLA PEDINA CON CUI ATTACCARE (A1-H8):");
			colonna1 = cella.toUpperCase().charAt(0);
			riga1 = cella.charAt(1);
			esito = tavolo.pedinaAttaccante(giocatore, riga1, colonna1);
			if (esito == -1) {
				System.out.println(intestazione + " LA PEDINA NELLA CELLA " + colonna1 + riga1 + " APPARTIENE ALL'AVVERSARIO, SELEZIONA UN'ALTRA CELLA");
			} else if (esito == 1) {
				System.out.println(intestazione + " LA PEDINA NELLA CELLA " + colonna1 + riga1 + " NON HA AVVERSARI ADIACENTI DA ATTACCARE, SELEZIONA UN'ALTRA PEDINA");
			} else if (esito == 2) {
				System.out.println(intestazione + " NELLA CELLA " + colonna1 + riga1 + " NON E' PRESENTE UNA PEDINA, SELEZIONA UN'ALTRA CELLA");
			} else if (esito == 3) {
				System.out.println(intestazione + " LA PEDINA NELLA CELLA " + colonna1 + riga1 + " NON E' UN ATTACCANTE, SELEZIONA UN'ALTRA PEDINA");
			}
		} while (esito != 0);

		char riga2;
		char colonna2;

		do {
			cella = selezioneCella(intestazione + " SELEZIONA LA CELLA DELLA PEDINA DA ATTACCARE (A1-H8):");
			colonna2 = cella.toUpperCase().charAt(0);
			riga2 = cella.charAt(1);
			esito = tavolo.pedinaAttaccabile(giocatore, riga1, colonna1, riga2, colonna2);
			if (esito == -1) {
				System.out.println(intestazione + " LA PEDINA NELLA CELLA " + colonna2 + riga2 + " NON APPARTIENE ALL'AVVERSARIO, SELEZIONA UN'ALTRA PEDINA");
			} else if (esito == 1) {
				System.out.println(intestazione + " LA PEDINA NELLA CELLA " + colonna2 + riga2 + " NON E' ATTACCABILE DALLA PEDINA NELLA CELLA " + colonna1 + riga1 + ", SELEZIONA UN'ALTRA PEDINA");
			} else if (esito == 2) {
				System.out.println(intestazione + " NELLA CELLA " + colonna2 + riga2 + " NON E' PRESENTE UNA PEDINA, SELEZIONA UN'ALTRA CELLA");
			}
		} while (esito != 0);

		tavolo.attaccaPedina(riga1, colonna1, riga2, colonna2);
		
	}
	
	/*@ requires giocatore == 'X' || giocatore == 'O';
	  @ requires intestazione != null &&
	  @ 		(intestazione.equals(new String("[X]")) || intestazione.equals(new String("[O]")));
	  @*/
	public void attaccareAvversario(char giocatore, String intestazione) throws IOException {
		
		String cella;
		int esito;
		char colonna;
		char riga;
		
		do {
			cella = selezioneCella(intestazione + " SELEZIONA LA CELLA DELLA PEDINA CON CUI ATTACCARE L'AVVERSARIO (A1-H8):");
			colonna = cella.toUpperCase().charAt(0);
			riga = cella.charAt(1);
			esito = tavolo.pedinaAttaccanteAvversario(giocatore, riga, colonna);
			if (esito == -1) {
				System.out.println(intestazione + " LA PEDINA NELLA CELLA " + colonna + riga + " APPARTIENE ALL'AVVERSARIO, SELEZIONA UN'ALTRA PEDINA");
			} else if (esito == 1) {
				System.out.println(intestazione + " LA PEDINA NELLA CELLA " + colonna + riga + " NON PUO' ATTACCARE L'AVVERSARIO, SELEZIONA UN'ALTRA PEDINA");
			} else if (esito == 2) {
				System.out.println(intestazione + " NELLA CELLA " + colonna + riga + " NON E' PRESENTE UNA PEDINA, SELEZIONA UN'ALTRA CELLA");
			} else if (esito == 3) {
				System.out.println(intestazione + " LA PEDINA NELLA CELLA " + colonna + riga + " NON E' UN ATTACCANTE, SELEZIONA UN'ALTRA PEDINA");
			}
		} while (esito != 0);

		tavolo.attaccaAvversario(giocatore, riga, colonna);
		
	}
	
	
	public void gioca() throws IOException {
		
		System.out.println("~~~ BENVENUTI IN MORTAL CHESS! ~~~");
		System.out.println();
		
		String entry;
		char nuovaPartita;
		
		do {
			
			System.out.println("~~~ PREPARAZIONE TAVOLO ... ~~~");
			System.out.println();
			
			tavolo.reset();
			impostaPunti();

			System.out.println();
			System.out.println("~~~ LA PARTITA HA INIZIO! ~~~");
			System.out.println();

			char giocatore = 'O';
			int turno = 1;
			String intestazione;
			char mossa;

			do {

				System.out.println("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ TURNO " + turno + " ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~");
				System.out.println();

				// stampo l'elenco delle pedine e il tavolo
				tavolo.print();

				// cambio turno
				giocatore = giocatore == 'X' ? 'O' : 'X';
				if (giocatore == 'O') turno++;
				intestazione = "[" + giocatore + "]";

				System.out.println("TURNO DEL GIOCATORE " + giocatore);
				System.out.println();

				// scelta mossa
				mossa = selezionaMossa(giocatore, intestazione);
				
				switch(mossa) {
					case '1': // posizionare una pedina
						posizionarePedina(giocatore, intestazione);
						break;
					case '2': // muovere una pedina
						muoverePedina(giocatore, intestazione);
						break;
					case '3': // unire due pedine
						unirePedine(giocatore, intestazione);
						break;
					case '4': // attaccare una pedina
						attaccarePedina(giocatore, intestazione);
						break;
					case '5': // attaccare l'avversario
						attaccareAvversario(giocatore, intestazione);
						break;
				}

				System.out.println();

			} while (!tavolo.partitaFinita());
			
			System.out.println("~~~ IL GIOCATORE " + tavolo.getVincitore() + " HA VINTO LA PARTITA! ~~~");
			System.out.println();

			do {
				System.out.println("~~~ INIZIARE UNA NUOVA PARTITA? (S/N) ~~~");
				entry = reader.readLine();
				nuovaPartita = entry.length() == 1 ? entry.charAt(0) : '0';
			} while (nuovaPartita != 'S' && nuovaPartita != 's' && nuovaPartita != 'N' && nuovaPartita != 'n');
			
			
		} while (nuovaPartita == 'S' || nuovaPartita == 's');
		
		System.out.println("~~~ CIAO! SPERO VI SIATE DIVERTITI! ALLA PROSSIMA PARTITA!~~~");
		
	}
	
}
