package org.deri.iris.storage;

import java.io.PrintWriter;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.sql.SQLFeatureNotSupportedException;
import java.util.logging.Logger;

import javax.sql.DataSource;

public class SimpleDataSource implements DataSource {
	private final String dbURI;
	private final String userName;
	private final String password;
	private boolean alreadyForNamed;

	public SimpleDataSource(String usr, String password) {
		this.userName = usr;
		this.password = password;
		this.alreadyForNamed = false;
		this.dbURI = "jdbc:oracle:thin:@pamir.dia.uniroma3.it:1521:Yaanii";
	}

	@Override
	public Connection getConnection(String username, String password) {
		synchronized (this) {
			if (!alreadyForNamed) {
				try {
					Class.forName("oracle.jdbc.driver.OracleDriver");
					alreadyForNamed = true;
				} catch (ClassNotFoundException e) {
					e.printStackTrace();
				}
			}
			try {
				return DriverManager.getConnection(dbURI, username, password);
			} catch (SQLException e) {
				e.printStackTrace();
			}
			return null;
		}
	}

	@Override
	public PrintWriter getLogWriter() throws SQLException {
		return null;
	}

	@Override
	public int getLoginTimeout() throws SQLException {
		return 0;
	}

	@Override
	public void setLogWriter(PrintWriter out) throws SQLException {

	}

	@Override
	public void setLoginTimeout(int seconds) throws SQLException {

	}

	@Override
	public boolean isWrapperFor(Class<?> iface) throws SQLException {
		return false;
	}

	@Override
	public <T> T unwrap(Class<T> iface) throws SQLException {
		return null;
	}

	@Override
	public Connection getConnection() throws SQLException {
		synchronized (this) {
			if (!alreadyForNamed) {
				try {
					Class.forName("oracle.jdbc.driver.OracleDriver");
					alreadyForNamed = true;
				} catch (ClassNotFoundException e) {
					e.printStackTrace();
				}
			}
			try {
				return DriverManager.getConnection(dbURI, userName, password);
			} catch (SQLException e) {
				e.printStackTrace();
			}
			return null;
		}
	}

	@Override
	public Logger getParentLogger() throws SQLFeatureNotSupportedException {
		// TODO Auto-generated method stub
		return null;
	}
}