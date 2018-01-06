/**
 * Copyright (c) 2010-2018 by the respective copyright holders.
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 */
package org.openhab.binding.zoneminder.handler;

import java.io.IOException;
import java.math.BigDecimal;
import java.security.GeneralSecurityException;
import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import javax.security.auth.login.FailedLoginException;

import org.apache.commons.lang.StringUtils;
import org.eclipse.smarthome.config.discovery.DiscoveryService;
import org.eclipse.smarthome.core.library.types.DecimalType;
import org.eclipse.smarthome.core.library.types.OnOffType;
import org.eclipse.smarthome.core.thing.Bridge;
import org.eclipse.smarthome.core.thing.Channel;
import org.eclipse.smarthome.core.thing.ChannelUID;
import org.eclipse.smarthome.core.thing.Thing;
import org.eclipse.smarthome.core.thing.ThingStatus;
import org.eclipse.smarthome.core.thing.ThingStatusDetail;
import org.eclipse.smarthome.core.thing.ThingStatusInfo;
import org.eclipse.smarthome.core.thing.ThingTypeUID;
import org.eclipse.smarthome.core.thing.ThingUID;
import org.eclipse.smarthome.core.thing.binding.BaseBridgeHandler;
import org.eclipse.smarthome.core.types.Command;
import org.eclipse.smarthome.core.types.RefreshType;
import org.eclipse.smarthome.core.types.State;
import org.eclipse.smarthome.core.types.UnDefType;
import org.openhab.binding.zoneminder.ZoneMinderConstants;
import org.openhab.binding.zoneminder.ZoneMinderProperties;
import org.openhab.binding.zoneminder.internal.DataRefreshPriorityEnum;
import org.openhab.binding.zoneminder.internal.config.ZoneMinderBridgeServerConfig;
import org.openhab.binding.zoneminder.internal.discovery.ZoneMinderDiscoveryService;
import org.osgi.framework.ServiceRegistration;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.google.common.collect.Sets;

import name.eskildsen.zoneminder.ILogEntry;
import name.eskildsen.zoneminder.IZoneMinderConnectionInfo;
import name.eskildsen.zoneminder.IZoneMinderDaemonStatus;
import name.eskildsen.zoneminder.IZoneMinderDiskUsage;
import name.eskildsen.zoneminder.IZoneMinderHostLoad;
import name.eskildsen.zoneminder.IZoneMinderHostVersion;
import name.eskildsen.zoneminder.IZoneMinderMonitorData;
import name.eskildsen.zoneminder.IZoneMinderServer;
import name.eskildsen.zoneminder.IZoneMinderSession;
import name.eskildsen.zoneminder.IZoneMinderVerification;
import name.eskildsen.zoneminder.ZoneMinderFactory;
import name.eskildsen.zoneminder.ZoneMinderVerification;
import name.eskildsen.zoneminder.api.config.ZoneMinderConfig;
import name.eskildsen.zoneminder.api.config.ZoneMinderConfigEnum;
import name.eskildsen.zoneminder.api.exception.ZoneMinderApiNotEnabledException;
import name.eskildsen.zoneminder.exception.ZoneMinderUrlNotFoundException;
import name.eskildsen.zoneminder.logging.LogLevel;

/**
 * Handler for a ZoneMinder Server.
 *
 * @author Martin S. Eskildsen
 *
 */
public class ZoneMinderServerBridgeHandler extends BaseBridgeHandler implements ZoneMinderHandler {

    public static final int TELNET_TIMEOUT = 5000;

    public static final Set<ThingTypeUID> SUPPORTED_THING_TYPES = Sets
            .newHashSet(ZoneMinderConstants.THING_TYPE_BRIDGE_ZONEMINDER_SERVER);

    private int failedAvailabilityCount = 0;
    /**
     * Logger
     */
    private final Logger logger = LoggerFactory.getLogger(getClass());

    private ZoneMinderDiscoveryService discoveryService = null;
    private ServiceRegistration discoveryRegistration = null;

    private ScheduledFuture<?> taskWatchDog = null;
    private int refreshFrequency = 0;
    private int refreshCycleCount = 0;

    /** Connection status for the bridge. */
    private boolean connected = false;

    private Runnable watchDogRunnable = new Runnable() {
        private int watchDogCount = -1;

        @Override
        public void run() {

            try {
                updateAvaliabilityStatus(zoneMinderConnection);

                // Only Discover if Bridge is online
                if (thing.getStatusInfo().getStatus() != ThingStatus.ONLINE) {
                    return;
                }

                // Check if autodiscovery is enabled
                boolean bAutoDiscover = getBridgeConfig().getAutodiscoverThings();

                if ((discoveryService != null) && (bAutoDiscover == true)) {
                    watchDogCount++;
                    // Run every two minutes
                    if ((watchDogCount % 8) == 0) {
                        discoveryService.startBackgroundDiscovery();
                        watchDogCount = 0;
                    }
                }

            } catch (Exception exception) {
                StackTraceElement ste = exception.getStackTrace()[0];
                logger.error("[WATCHDOG]: Server run(): StackTrace: File='{}', Line='{}', Method='{}', Exception: {}",
                        ste.getFileName(), ste.getLineNumber(), ste.getMethodName(), exception.getMessage());
            }
        }
    };

    /**
     * Local copies of last fetched values from ZM
     */
    private String channelCpuLoad = "";
    private String channelDiskUsage = "";

    Boolean isInitialized = false;

    private IZoneMinderSession _zoneMinderSession = null;
    private IZoneMinderConnectionInfo zoneMinderConnection = null;
    private String zoneMinderLoggerUuid = "";

    private Lock lockSession = new ReentrantLock();

    private ScheduledFuture<?> taskRefreshData = null;
    private ScheduledFuture<?> taskPriorityRefreshData = null;

    private Runnable refreshDataRunnable = new Runnable() {
        @Override
        public void run() {
            try {
                boolean fetchDiskUsage = false;

                if (!isOnline()) {
                    logger.debug("{}: Bridge '{}' is not online skipping refresh", getLogIdentifier(), thing.getUID());
                    return;
                }

                refreshCycleCount++;

                int iMaxCycles;
                boolean resetCount = false;
                boolean doRefresh = false;

                // Disk Usage is disabled
                if (getBridgeConfig().getRefreshIntervalLowPriorityTask() == 0) {
                    iMaxCycles = getBridgeConfig().getRefreshInterval();
                    resetCount = true;
                    doRefresh = true;

                } else {
                    iMaxCycles = getBridgeConfig().getRefreshIntervalLowPriorityTask() * 60;
                    doRefresh = true;
                    if ((refreshCycleCount * refreshFrequency) >= (getBridgeConfig().getRefreshIntervalLowPriorityTask()
                            * 60)) {
                        fetchDiskUsage = true;
                        resetCount = true;

                    }
                }

                logger.debug(
                        "{}: Running Refresh data task count='{}', freq='{}', max='{}', interval='{}', intervalLow='{}'",
                        getLogIdentifier(), refreshCycleCount, refreshFrequency, iMaxCycles,
                        getBridgeConfig().getRefreshInterval(), getBridgeConfig().getRefreshIntervalLowPriorityTask());

                if (doRefresh) {

                    if (resetCount == true) {
                        refreshCycleCount = 0;
                    }

                    logger.debug("{}: 'refreshDataRunnable()': (diskUsage='{}')", getLogIdentifier(), fetchDiskUsage);

                    refreshThing(fetchDiskUsage);
                }

            } catch (Exception exception) {
                logger.error("{}: monitorRunnable::run(): Exception: ", getLogIdentifier(), exception);
            }
        }
    };

    private Runnable refreshPriorityDataRunnable = new Runnable() {

        @Override
        public void run() {
            try {

                // Make sure priority updates is done
                for (Thing thing : getThing().getThings()) {
                    try {

                        if (thing.getThingTypeUID().equals(ZoneMinderConstants.THING_TYPE_THING_ZONEMINDER_MONITOR)) {
                            Thing thingMonitor = thing;

                            ZoneMinderBaseThingHandler thingHandler = (ZoneMinderBaseThingHandler) thing.getHandler();
                            if (thingHandler != null) {

                                if (thingHandler.getRefreshPriority() == DataRefreshPriorityEnum.HIGH_PRIORITY) {
                                    logger.debug("[MONITOR-{}]: RefreshPriority is High Priority",
                                            thingHandler.getZoneMinderId());
                                    thingHandler.refreshThing(DataRefreshPriorityEnum.HIGH_PRIORITY);
                                }
                            } else {
                                logger.debug(
                                        "[MONITOR]: refreshThing not called for monitor, since thingHandler is 'null'");

                            }
                        }

                    } catch (NullPointerException ex) {
                        // This isn't critical (unless it comes over and over). There seems to be a bug so that a
                        // null
                        // pointer exception is coming every now and then.
                        // HAve to find the reason for that. Until thenm, don't Spamm
                        logger.error(
                                "[MONITOR]: Method 'refreshThing()' for Bridge failed for thing='{}' - Exception: ",
                                thing.getUID(), ex);
                    } catch (Exception ex) {
                        logger.error(
                                "[MONITOR]: Method 'refreshThing()' for Bridge failed for thing='{}' - Exception: ",
                                thing.getUID(), ex);
                    }
                }

            } catch (Exception exception) {
                logger.error("[MONITOR]: monitorRunnable::run(): Exception: ", exception);
            }
        }
    };

    /**
     * Constructor
     *
     *
     * @param bridge
     *            Bridge object representing a ZoneMinder Server
     */
    public ZoneMinderServerBridgeHandler(Bridge bridge) {
        super(bridge);

        logger.info("{}: Starting ZoneMinder Server Bridge Handler (Bridge='{}')", getLogIdentifier(),
                bridge.getBridgeUID());
    }

    /**
     * Initializes the bridge.
     */
    @Override
    public void initialize() {
        logger.debug("[BRIDGE]: About to initialize bridge " + ZoneMinderConstants.BRIDGE_ZONEMINDER_SERVER);
        try {
            updateStatus(ThingStatus.OFFLINE);
            logger.info("BRIDGE: ZoneMinder Server Bridge Handler Initialized");
            logger.debug("BRIDGE:    HostName:           {}", getBridgeConfig().getHostName());
            logger.debug("BRIDGE:    Protocol:           {}", getBridgeConfig().getProtocol());
            logger.debug("BRIDGE:    Port HTTP(S)        {}", getBridgeConfig().getHttpPort());
            logger.debug("BRIDGE:    Port Telnet         {}", getBridgeConfig().getTelnetPort());
            logger.debug("BRIDGE:    Portal Path         {}", getBridgeConfig().getServerBasePath());
            logger.debug("BRIDGE:    API Path            {}", getBridgeConfig().getServerApiPath());
            logger.debug("BRIDGE:    User:               {}", getBridgeConfig().getUserName());
            logger.debug("BRIDGE:    Refresh interval:   {}", getBridgeConfig().getRefreshInterval());
            logger.debug("BRIDGE:    Low  prio. refresh: {}", getBridgeConfig().getRefreshIntervalLowPriorityTask());
            logger.debug("BRIDGE:    Autodiscovery:      {}", getBridgeConfig().getAutodiscoverThings());

            closeConnection();

            zoneMinderLoggerUuid = ZoneMinderFactory.createLogger();
            zoneMinderConnection = ZoneMinderFactory.CreateConnection(getBridgeConfig().getProtocol(),
                    getBridgeConfig().getHostName(), getBridgeConfig().getHttpPort(), getBridgeConfig().getTelnetPort(),
                    getBridgeConfig().getUserName(), getBridgeConfig().getPassword(),
                    getBridgeConfig().getServerBasePath(), getBridgeConfig().getServerApiPath(), 10000,
                    zoneMinderLoggerUuid);

            // Find a better way to let loglevel follow openHAB
            zoneMinderConnection.setLogLevel(LogLevel.INFO);

            taskRefreshData = null;
            taskPriorityRefreshData = null;

        } catch (Exception ex) {
            if (zoneMinderConnection == null) {
                logger.error(
                        "[BRIDGE]: 'ZoneMinderServerBridgeHandler' general configuration error occurred. Failed to initialize. Exception='{}'",
                        ex.getMessage());
                updateStatus(ThingStatus.OFFLINE, ThingStatusDetail.CONFIGURATION_ERROR);
            } else {
                logger.error("[BRIDGE]: 'ZoneMinderServerBridgeHandler' failed to initialize. Exception='{}'",
                        ex.getMessage());
                updateStatus(ThingStatus.OFFLINE, ThingStatusDetail.HANDLER_INITIALIZING_ERROR);
            }

            isInitialized = false;
            return;
        }

        startWatchDogTask();
        isInitialized = true;

    }

    protected IZoneMinderSession aquireSession() {
        lockSession.lock();
        return _zoneMinderSession;
    }

    protected void releaseSession() {
        lockSession.unlock();
    }

    /**
     * Method to find the lowest possible refresh rate (based on configuration)
     *
     * @param refreshRate
     * @return
     */
    protected int calculateCommonRefreshFrequency(int refreshRate) {
        // Check if 30, 15, 10 or 5 seconds is possible
        if ((refreshRate % 30) == 0) {
            return 30;
        } else if ((refreshRate % 15) == 0) {
            return 15;
        } else if ((refreshRate % 10) == 0) {
            return 10;
        } else if ((refreshRate % 5) == 0) {
            return 5;
        }

        // Hmm, didn't find a obvious shared value. Run every second...
        return 1;

    }

    protected void startWatchDogTask() {
        taskWatchDog = startTask(watchDogRunnable, 0, 15, TimeUnit.SECONDS);
    }

    protected void stopWatchDogTask() {
        stopTask(taskWatchDog);
        taskWatchDog = null;
    }

    /**
     */
    @Override
    public void dispose() {
        try {
            logger.debug("{}: Stop polling of ZoneMinder Server API", getLogIdentifier());

            logger.info("{}: Stopping Discovery service", getLogIdentifier());
            // Remove the discovery service
            if (discoveryService != null) {
                discoveryService.deactivate();
                discoveryService = null;
            }

            if (discoveryRegistration != null) {
                discoveryRegistration.unregister();
                discoveryRegistration = null;
            }

            logger.info("{}: Stopping WatchDog task", getLogIdentifier());
            stopWatchDogTask();

            logger.info("{}: Stopping refresh data task", getLogIdentifier());
            stopTask(taskRefreshData);
        } catch (Exception ex) {
        }
    }

    protected String getThingId() {
        return getThing().getUID().getId();
    }

    @Override
    public String getZoneMinderId() {

        return getThing().getUID().getAsString();
    }

    @Override
    public void channelLinked(ChannelUID channelUID) {
        // can be overridden by subclasses
        ThingUID s1 = getThing().getUID();
        ThingTypeUID s2 = getThing().getThingTypeUID();
        logger.debug("{}: Channel '{}' was linked to '{}'", getLogIdentifier(), channelUID.getAsString(),
                this.thing.getThingTypeUID());
    }

    @Override
    public void channelUnlinked(ChannelUID channelUID) {
        // can be overridden by subclasses
        logger.debug("{}: Channel '{}' was unlinked from '{}'", getLogIdentifier(), channelUID.getAsString(),
                this.thing.getThingTypeUID());
    }

    protected ArrayList<IZoneMinderMonitorData> getMonitors(IZoneMinderSession session) {

        if (isConnected()) {
            return ZoneMinderFactory.getServerProxy(session).getMonitors();
        }

        return new ArrayList<IZoneMinderMonitorData>();

    }

    protected ZoneMinderBridgeServerConfig getBridgeConfig() {
        return this.getConfigAs(ZoneMinderBridgeServerConfig.class);
    }

    /**
    *
    */
    public ZoneMinderBaseThingHandler getZoneMinderThingHandlerFromZoneMinderId(ThingTypeUID thingTypeUID,
            String zoneMinderId) {

        // Inform thing handlers of connection
        List<Thing> things = getThing().getThings();

        for (Thing thing : things) {
            ZoneMinderBaseThingHandler thingHandler = (ZoneMinderBaseThingHandler) thing.getHandler();
            if ((thingHandler.getZoneMinderId().equals(zoneMinderId))
                    && (thing.getThingTypeUID().equals(thingTypeUID))) {
                return thingHandler;
            }
        }
        return null;
    }

    @Override
    public void handleCommand(ChannelUID channelUID, Command command) {
        logger.debug("{}: Update '{}' with '{}'", getLogIdentifier(), channelUID.getAsString(), command.toString());
    }

    protected synchronized void refreshThing(boolean fetchDiskUsage) {

        logger.debug("{}: 'refreshThing()': Thing='{}'!", getLogIdentifier(), this.getThing().getUID());

        List<Channel> channels = getThing().getChannels();
        List<Thing> things = getThing().getThings();

        try {
            IZoneMinderServer zoneMinderServerProxy = ZoneMinderFactory.getServerProxy(aquireSession());
            if (zoneMinderServerProxy == null) {
                logger.warn("{}:  Could not obtain ZonerMinderServerProxy ", getLogIdentifier());

                // Make sure old data is cleared
                channelCpuLoad = "";
                channelDiskUsage = "";

            } else if (isConnected()) {
                /*
                 * Fetch data for Bridge
                 */
                IZoneMinderHostLoad hostLoad = null;
                try {
                    hostLoad = zoneMinderServerProxy.getHostCpuLoad();
                    logger.debug("{}: URL='{}' ResponseCode='{}' ResponseMessage='{}'", getLogIdentifier(),
                            zoneMinderServerProxy.getHttpUrl(), zoneMinderServerProxy.getHttpResponseCode(),
                            zoneMinderServerProxy.getHttpResponseMessage());

                } catch (FailedLoginException | ZoneMinderUrlNotFoundException | IOException ex) {
                    logger.error("{}: Exception thrown in call to ZoneMinderHostLoad ('{}')", getLogIdentifier(), ex);
                }

                if (hostLoad == null) {
                    logger.warn("{}: ZoneMinderHostLoad dataset could not be obtained (received 'null')",
                            getLogIdentifier());
                } else if (hostLoad.getHttpResponseCode() != 200) {
                    logger.warn(
                            "BRIDGE [{}]: ZoneMinderHostLoad dataset could not be obtained (HTTP Response: Code='{}', Message='{}')",
                            getThingId(), hostLoad.getHttpResponseCode(), hostLoad.getHttpResponseMessage());

                } else {
                    channelCpuLoad = hostLoad.getCpuLoad().toString();
                }

                if (fetchDiskUsage) {
                    IZoneMinderDiskUsage diskUsage = null;
                    try {
                        diskUsage = zoneMinderServerProxy.getHostDiskUsage();
                        logger.debug("{}: URL='{}' ResponseCode='{}' ResponseMessage='{}'", getLogIdentifier(),
                                zoneMinderServerProxy.getHttpUrl(), zoneMinderServerProxy.getHttpResponseCode(),
                                zoneMinderServerProxy.getHttpResponseMessage());
                    } catch (Exception ex) {
                        logger.error("{}: Exception thrown in call to ZoneMinderDiskUsage ('{}')", getLogIdentifier(),
                                ex);
                    }

                    if (diskUsage == null) {
                        logger.warn("{}: ZoneMinderDiskUsage dataset could not be obtained (received 'null')",
                                getLogIdentifier());
                    } else if (hostLoad.getHttpResponseCode() != 200) {
                        logger.warn(
                                "{}: ZoneMinderDiskUsage dataset could not be obtained (HTTP Response: Code='{}', Message='{}')",
                                getLogIdentifier(), hostLoad.getHttpResponseCode(), hostLoad.getHttpResponseMessage());

                    } else {
                        channelDiskUsage = diskUsage.getDiskUsage();
                    }
                }

            } else {

                // Make sure old data is cleared
                channelCpuLoad = "";
                channelDiskUsage = "";
            }
        } finally {

            releaseSession();

        }
        /*
         * Update all channels on Bridge
         */
        for (Channel channel : channels) {
            updateChannel(channel.getUID());
        }

        /*
         * Request Things attached to Bridge to refresh
         */
        for (Thing thing : things) {
            try {

                if (thing.getThingTypeUID().equals(ZoneMinderConstants.THING_TYPE_THING_ZONEMINDER_MONITOR)) {
                    Thing thingMonitor = thing;
                    ZoneMinderBaseThingHandler thingHandler = (ZoneMinderBaseThingHandler) thing.getHandler();

                    thingHandler.refreshThing(DataRefreshPriorityEnum.SCHEDULED);
                }

            } catch (NullPointerException ex) {
                // This isn't critical (unless it comes over and over). There seems to be a bug so that a null
                // pointer exception is coming every now and then.
                // Have to find the reason for that. Until then, don't Spamm
                logger.debug("{}: Method 'refreshThing()' for Bridge {} failed for thing='{}' - Exception='{}'",
                        getLogIdentifier(), this.getZoneMinderId(), thing.getUID(), ex.getMessage());

                // Other exceptions has to be shown as errors
            } catch (Exception ex) {
                logger.error("{}: Method 'refreshThing()' for Bridge {} failed for thing='{}' - Exception='{}'",
                        getLogIdentifier(), this.getZoneMinderId(), thing.getUID(), ex.getMessage());
            }
        }

    }

    private void processZoneMinderQueryLog(List<ILogEntry> entries) {

        for (ILogEntry entry : entries) {
            String message = String.format("%s: %s", entry.getLogLevel(), entry.toString());
            logger.debug(message);
        }
    }

    /**
     * Returns connection status.
     */
    public synchronized Boolean isConnected() {
        return connected;
    }

    public boolean isOnline() {

        ThingStatusInfo statusInfo = getThing().getStatusInfo();
        return (statusInfo.getStatus() == ThingStatus.ONLINE) ? true : false;
    }

    private synchronized boolean getConnected() {
        return this.connected;
    }

    /**
     * Set connection status.
     *
     * @param connected
     */
    private synchronized void setConnected(boolean connected) {

        if (this.connected != connected) {
            lockSession.lock();
            try {
                if (connected) {
                    try {
                        _zoneMinderSession = ZoneMinderFactory.CreateSession(zoneMinderConnection);
                    } catch (FailedLoginException | IllegalArgumentException | IOException
                            | ZoneMinderUrlNotFoundException e) {
                        logger.error("BRIDGE [{}]: Call to setConencted failed with exception '{}'", getThingId(),
                                e.getMessage());
                    } catch (ZoneMinderApiNotEnabledException e) {
                        logger.error("BRIDGE [{}]: ZoneMinderServer has not enabled API - Exception '{}'",
                                e.getMessage());
                    } catch (Exception e) {
                        logger.error(
                                "BRIDGE [{}]: Error thrown from ZoneMinderServer when creating a session - Exception '{}'",
                                e.getMessage());
                    }
                } else {
                    _zoneMinderSession = null;
                }
            } finally {
                this.connected = connected;
                lockSession.unlock();
            }

        }

    }


    /**
     * Set channel 'bridge_connection'.
     *
     * @param connected
     */
    private void setBridgeConnectionStatus(boolean connected) {
        logger.debug(" {}: setBridgeConnection(): Set Bridge to {}", getLogIdentifier(),
                connected ? ThingStatus.ONLINE : ThingStatus.OFFLINE);

        Bridge bridge = getBridge();
        if (bridge != null) {
            ThingStatus status = bridge.getStatus();
            logger.debug("{}: Bridge ThingStatus is: {}", getLogIdentifier(), status);
        }

        setConnected(connected);
    }

    /**
     * Set channel 'bridge_connection'.
     *
     * @param connected
     */
    private boolean getBridgeConnectionStatus() {
        return getConnected();
    }

    /**
     * Runs when connection established.
     *
     * @throws ZoneMinderUrlNotFoundException
     * @throws IOException
     * @throws GeneralSecurityException
     * @throws IllegalArgumentException
     */
    public void onConnected() {
        logger.debug("BRIDGE [{}]: onConnected(): Bridge Connected!", getThingId());
        setConnected(true);
        onBridgeConnected(this, zoneMinderConnection);

        // Inform thing handlers of connection
        List<Thing> things = getThing().getThings();

        for (Thing thing : things) {
            ZoneMinderBaseThingHandler thingHandler = (ZoneMinderBaseThingHandler) thing.getHandler();

            if (thingHandler != null) {
                try {
                    thingHandler.onBridgeConnected(this, zoneMinderConnection);
                } catch (IllegalArgumentException | GeneralSecurityException | IOException
                        | ZoneMinderUrlNotFoundException e) {
                    logger.error("{}: onConnected() failed - Exceprion: {}", getLogIdentifier(), e.getMessage());
                }
                logger.debug("{}: onConnected(): Bridge - {}, Thing - {}, Thing Handler - {}", getLogIdentifier(),
                        thing.getBridgeUID(), thing.getUID(), thingHandler);
            }
        }
    }

    /**
     * Runs when disconnected.
     */
    private void onDisconnected() {
        logger.debug("{}: onDisconnected(): Bridge Disconnected!", getLogIdentifier());
        setConnected(false);
        onBridgeDisconnected(this);

        // Inform thing handlers of disconnection
        List<Thing> things = getThing().getThings();

        for (Thing thing : things) {
            ZoneMinderBaseThingHandler thingHandler = (ZoneMinderBaseThingHandler) thing.getHandler();

            if (thingHandler != null) {
                thingHandler.onBridgeDisconnected(this);
                logger.debug("{}: onDisconnected(): Bridge - {}, Thing - {}, Thing Handler - {}", getLogIdentifier(),
                        thing.getBridgeUID(), thing.getUID(), thingHandler);
            }
        }
    }

    @Override
    public void updateAvaliabilityStatus(IZoneMinderConnectionInfo connection) {

        ThingStatus newStatus = ThingStatus.OFFLINE;
        ThingStatusDetail statusDetail = ThingStatusDetail.NONE;
        String statusDescription = "";

        boolean _isOnline = false;

        ThingStatus prevStatus = getThing().getStatus();
        try {
            // Just perform a health check to see if we are still connected
            if (prevStatus == ThingStatus.ONLINE) {
                try {
                    lockSession.lock();

                    if (_zoneMinderSession == null) {
                        newStatus = ThingStatus.ONLINE;
                        statusDetail = ThingStatusDetail.NONE;
                        statusDescription = "";
                        updateBridgeStatus(newStatus, statusDetail, statusDescription);
                        return;
                    } else if (!_zoneMinderSession.isConnected()) {
                        newStatus = ThingStatus.OFFLINE;
                        statusDetail = ThingStatusDetail.COMMUNICATION_ERROR;
                        statusDescription = "Session lost connection to ZoneMinder Server";
                        updateBridgeStatus(newStatus, statusDetail, statusDescription);

                        return;
                    }

                    else if (!_zoneMinderSession.isAuthenticated()) {
                        newStatus = ThingStatus.OFFLINE;
                        statusDetail = ThingStatusDetail.COMMUNICATION_ERROR;
                        statusDescription = "Not authenticated in ZoneMinder Server";
                        updateBridgeStatus(newStatus, statusDetail, statusDescription);
                        return;
                    }
                } finally {
                    lockSession.unlock();
                }

                // Now try to query daemonStatus. If it returns a NPE, connection was lost. Let it retry a couple of
                // times before disconnecting.
                IZoneMinderDaemonStatus daemonStatus = null;
                try {
                    // Get Server proxy
                    IZoneMinderServer serverProxy = ZoneMinderFactory.getServerProxy(aquireSession());
                    processZoneMinderQueryLog(ZoneMinderFactory.getLogEntries(zoneMinderLoggerUuid));

                    daemonStatus = serverProxy.getHostDaemonCheckState();
                } catch (NullPointerException npe) {
                    failedAvailabilityCount++;
                    try {
                        logger.debug("{}: Connection to ZoneMinder server was lost, trying to reconnect.",
                                getLogIdentifier());
                        _zoneMinderSession = ZoneMinderFactory.CreateSession(connection);
                    } catch (ZoneMinderApiNotEnabledException e) {
                        // Intentional left blank, since we know that Api is enabled at this stage
                    }
                } finally {
                    releaseSession();
                }

                if (daemonStatus != null) {
                    failedAvailabilityCount = 0;
                } else {
                    if (failedAvailabilityCount > 3) {
                        newStatus = ThingStatus.OFFLINE;
                        statusDetail = ThingStatusDetail.COMMUNICATION_ERROR;
                        logger.error("{}: Lost connection to ZoneMinder server. Bridge state changed to 'OFFLINE'",
                                getLogIdentifier());
                        statusDescription = "Lost connection to ZoneMinder server";
                        updateBridgeStatus(newStatus, statusDetail, statusDescription);
                    }
                    return;
                }

                // If service isn't running OR we received a http responsecode other than 200, assume we are offline
                if ((!daemonStatus.getStatus()) || (daemonStatus.getHttpResponseCode() != 200)) {
                    newStatus = ThingStatus.OFFLINE;
                    statusDetail = ThingStatusDetail.COMMUNICATION_ERROR;
                    statusDescription = "ZoneMinder Server Daemon not running";

                    logger.debug("{}: {} (state='{}' and ResponseCode='{}')", getLogIdentifier(), statusDescription,
                            daemonStatus.getStatus(), daemonStatus.getHttpResponseCode());
                    updateBridgeStatus(newStatus, statusDetail, statusDescription);
                    return;
                }

                newStatus = ThingStatus.ONLINE;
                statusDetail = ThingStatusDetail.NONE;
                statusDescription = "";

                // Ask all child things to update their Availability Status
                for (Thing thing : getThing().getThings()) {
                    ZoneMinderBaseThingHandler thingHandler = (ZoneMinderBaseThingHandler) thing.getHandler();
                    if (thingHandler instanceof ZoneMinderThingMonitorHandler) {
                        try {
                            thingHandler.updateAvaliabilityStatus(zoneMinderConnection);
                        } catch (Exception ex) {
                            logger.debug("{}: Failed to call 'updateAvailabilityStatus()' for '{}'", getLogIdentifier(),
                                    thingHandler.getThing().getUID());
                        }
                    }

                }

            }
            // If we are OFFLINE, check everything
            else if (prevStatus == ThingStatus.OFFLINE) {

                // Just wait until we are finished initializing
                if (isInitialized == false) {
                    return;
                }

                ZoneMinderBridgeServerConfig config = getBridgeConfig();
                IZoneMinderVerification verification = ZoneMinderVerification.getInstance(connection);

                // Check if server Bridge configuration is valid
                if (config == null) {
                    newStatus = ThingStatus.OFFLINE;
                    statusDetail = ThingStatusDetail.CONFIGURATION_ERROR;
                    statusDescription = "Configuration not found";
                    updateBridgeStatus(newStatus, statusDetail, statusDescription);
                    return;

                } else if (config.getHostName() == null) {
                    newStatus = ThingStatus.OFFLINE;
                    statusDetail = ThingStatusDetail.CONFIGURATION_ERROR;
                    statusDescription = "Host not found in configuration";
                    updateBridgeStatus(newStatus, statusDetail, statusDescription);
                    return;
                } else if (config.getProtocol() == null) {
                    newStatus = ThingStatus.OFFLINE;
                    statusDetail = ThingStatusDetail.CONFIGURATION_ERROR;
                    statusDescription = "Unknown protocol in configuration";
                    updateBridgeStatus(newStatus, statusDetail, statusDescription);
                    return;
                }

                else if (config.getHttpPort() == null) {
                    newStatus = ThingStatus.OFFLINE;
                    statusDetail = ThingStatusDetail.CONFIGURATION_ERROR;
                    statusDescription = "Invalid HTTP port";
                    updateBridgeStatus(newStatus, statusDetail, statusDescription);
                    return;
                }

                else if (config.getTelnetPort() == null) {
                    newStatus = ThingStatus.OFFLINE;
                    statusDetail = ThingStatusDetail.CONFIGURATION_ERROR;
                    statusDescription = "Invalid telnet port";
                    updateBridgeStatus(newStatus, statusDetail, statusDescription);
                    return;
                }

                boolean isApiEnabled = verification.isApiEnabled();
                processZoneMinderQueryLog(ZoneMinderFactory.getLogEntries(zoneMinderLoggerUuid));
                if (!isApiEnabled) {
                    newStatus = ThingStatus.OFFLINE;
                    statusDetail = ThingStatusDetail.CONFIGURATION_ERROR;
                    statusDescription = "ZoneMinder Server 'OPT_USE_API' not enabled";
                    updateBridgeStatus(newStatus, statusDetail, statusDescription);
                    return;
                }

                /*
                 * Now we will try to establish a session
                 */
                IZoneMinderSession curSession = null;
                try {
                    curSession = ZoneMinderFactory.CreateSession(connection);
                    processZoneMinderQueryLog(ZoneMinderFactory.getLogEntries(zoneMinderLoggerUuid));
                } catch (FailedLoginException failedLoginEx) {
                    newStatus = ThingStatus.OFFLINE;
                    statusDetail = ThingStatusDetail.CONFIGURATION_ERROR;
                    statusDescription = "Cannot access ZoneMinder Server. Check provided usercredentials";

                    if (prevStatus != ThingStatus.OFFLINE) {
                        logger.error("{}: Bridge OFFLINE because of '{}' Exception='{}'", getLogIdentifier(),
                                statusDescription, failedLoginEx.getMessage());
                    }

                    updateBridgeStatus(newStatus, statusDetail, statusDescription);
                    curSession = null;
                    return;
                } catch (IllegalArgumentException | IOException | ZoneMinderApiNotEnabledException
                        | ZoneMinderUrlNotFoundException ex) {
                    logger.error("{}: Create Session failed with exception {}", getLogIdentifier(), ex.getMessage());

                    newStatus = ThingStatus.OFFLINE;
                    statusDetail = ThingStatusDetail.COMMUNICATION_ERROR;
                    statusDescription = "Failed to connect. (Check Log)";

                    if (prevStatus != ThingStatus.OFFLINE) {
                        logger.error("{}: Bridge OFFLINE because of '{}' Exception='{}'", getLogIdentifier(),
                                statusDescription, ex.getMessage());
                    }
                    updateBridgeStatus(newStatus, statusDetail, statusDescription);
                    return;
                }

                IZoneMinderServer serverProxy = ZoneMinderFactory.getServerProxy(curSession);

                // Check if server API can be accessed
                if (!verifyHostDaemonStatus(curSession)) {
                    newStatus = ThingStatus.OFFLINE;
                    statusDetail = ThingStatusDetail.CONFIGURATION_ERROR;
                    statusDescription = "ZoneMinder Server Daemon not running";
                    updateBridgeStatus(newStatus, statusDetail, statusDescription);
                    return;
                }
                // Verify that 'OPT_TRIGGER' is set to true in ZoneMinder
                else if (!serverProxy.isTriggerOptionEnabled()) {
                    newStatus = ThingStatus.OFFLINE;
                    statusDetail = ThingStatusDetail.CONFIGURATION_ERROR;
                    statusDescription = "ZoneMinder Server option 'OPT_TRIGGERS' not enabled";
                    updateBridgeStatus(newStatus, statusDetail, statusDescription);
                    return;
                } else {
                    // Seems like everything is as we want it :-)
                    _isOnline = true;
                }

                lockSession.lock();
                if (_isOnline == true) {
                    _zoneMinderSession = curSession;
                    newStatus = ThingStatus.ONLINE;
                    statusDetail = ThingStatusDetail.NONE;
                    statusDescription = "";

                } else {
                    _zoneMinderSession = null;
                    newStatus = ThingStatus.OFFLINE;
                }
                lockSession.unlock();
            }

        }

        catch (

        Exception ex) {
            newStatus = ThingStatus.OFFLINE;
            statusDetail = ThingStatusDetail.COMMUNICATION_ERROR;
            logger.error("{}: Exception occurred in updateAvailabilityStatus Exception='{}'", getLogIdentifier(),
                    ex.getMessage());
            statusDescription = "Error occurred (Check log)";

        }

        updateBridgeStatus(newStatus, statusDetail, statusDescription);
    }

    protected void updateBridgeStatus(ThingStatus newStatus, ThingStatusDetail statusDetail, String statusDescription) {
        ThingStatusInfo curStatusInfo = thing.getStatusInfo();
        String curDescription = StringUtils.isBlank(curStatusInfo.getDescription()) ? ""
                : curStatusInfo.getDescription();

        // Status changed
        if ((curStatusInfo.getStatus() != newStatus) || (curStatusInfo.getStatusDetail() != statusDetail)
                || (curDescription != statusDescription)) {

            logger.info("{}: Bridge status changed from '{}' to '{}'", getLogIdentifier(), thing.getStatus(),
                    newStatus);

            if ((newStatus == ThingStatus.ONLINE) && (curStatusInfo.getStatus() != ThingStatus.ONLINE)) {
                try {
                    setBridgeConnectionStatus(true);
                    onConnected();
                } catch (IllegalArgumentException e) {
                    // Just ignore that here
                }
            } else if ((newStatus == ThingStatus.OFFLINE) && (curStatusInfo.getStatus() != ThingStatus.OFFLINE)) {
                try {
                    setBridgeConnectionStatus(false);
                    onDisconnected();
                } catch (IllegalArgumentException e) {
                    // Just ignore that here
                }

            }
            // Update Status correspondingly
            if ((newStatus == ThingStatus.OFFLINE) && (statusDetail != ThingStatusDetail.NONE)) {
                updateStatus(newStatus, statusDetail, statusDescription);
            } else {
                updateStatus(newStatus);
            }

            // Ask all child things to update their Availability Status, since Bridge has changed
            for (Thing thing : getThing().getThings()) {
                ZoneMinderBaseThingHandler thingHandler = (ZoneMinderBaseThingHandler) thing.getHandler();
                if (thingHandler instanceof ZoneMinderThingMonitorHandler) {
                    try {
                        thingHandler.updateAvaliabilityStatus(zoneMinderConnection);
                    } catch (Exception ex) {
                        logger.debug("{}: Failed to call 'updateAvailabilityStatus()' for '{}'", getLogIdentifier(),
                                thingHandler.getThing().getUID());
                    }
                }

            }

        }
    }

    protected boolean isZoneMinderUrl(IZoneMinderConnectionInfo connection) {

        try {
            return ZoneMinderFactory.isZoneMinderUrl(connection);
        } catch (IllegalArgumentException | ZoneMinderApiNotEnabledException e) {

        }
        return false;
    }

    protected boolean isZoneMinderLoginValid(IZoneMinderConnectionInfo connection) {
        try {
            boolean isvalid = ZoneMinderFactory.validateLogin(connection);
            processZoneMinderQueryLog(ZoneMinderFactory.getLogEntries(zoneMinderLoggerUuid));
            return isvalid;
        } catch (Exception e) {

        } catch (ZoneMinderApiNotEnabledException e) {
            // TODO:: Error handling
        }
        return false;
    }

    protected boolean verifyHostDaemonStatus(IZoneMinderSession session) {
        IZoneMinderServer serverProxy = ZoneMinderFactory.getServerProxy(session);
        IZoneMinderDaemonStatus daemonStatus = serverProxy.getHostDaemonCheckState();
        processZoneMinderQueryLog(ZoneMinderFactory.getLogEntries(zoneMinderLoggerUuid));

        return daemonStatus.getStatus();
    }

    @Override
    public void updateChannel(ChannelUID channel) {
        State state = null;
        try {

            switch (channel.getId()) {
                case ZoneMinderConstants.CHANNEL_ONLINE:
                    updateState(channel, (isOnline() ? OnOffType.ON : OnOffType.OFF));
                    break;

                case ZoneMinderConstants.CHANNEL_SERVER_DISKUSAGE:
                    state = getServerDiskUsageState();
                    break;

                case ZoneMinderConstants.CHANNEL_SERVER_CPULOAD:
                    state = getServerCpuLoadState();
                    break;

                default:
                    logger.warn("{}: updateChannel(): Server '{}': No handler defined for channel='{}'",
                            getLogIdentifier(), thing.getLabel(), channel.getAsString());
                    break;
            }
            processZoneMinderQueryLog(ZoneMinderFactory.getLogEntries(zoneMinderLoggerUuid));

            if (state != null) {
                logger.debug("{}: BridgeHandler.updateChannel(): Updating channel '{}' to state='{}'",
                        getLogIdentifier(), channel.getId(), state.toString());
                updateState(channel.getId(), state);
            }
        } catch (Exception ex) {

            logger.error("{}: Error when 'updateChannel()' was called for thing='{}' (Exception='{}'",
                    getLogIdentifier(), channel.getId(), ex.getMessage());

        }
    }

    protected boolean openConnection() {
        boolean connected = false;
        if (isConnected() == false) {
            logger.debug("{}: Connecting Bridge to ZoneMinder Server", getLogIdentifier());

            try {
                if (isConnected()) {
                    closeConnection();
                }
                setConnected(connected);

                logger.info("{}: Connecting to ZoneMinder Server (result='{}'", getLogIdentifier(), connected);

            } catch (Exception exception) {
                logger.error("{}: openConnection(): Exception: ", getLogIdentifier(), exception);
                setConnected(false);
            } finally {
                if (isConnected() == false) {
                    closeConnection();
                }
            }

        }
        return isConnected();
    }

    synchronized void closeConnection() {
        try {
            logger.debug("{}: closeConnection(): Closed HTTP Connection!", getLogIdentifier());
            setConnected(false);

        } catch (Exception exception) {
            logger.error("{}: closeConnection(): Error closing connection - {}", getLogIdentifier(),
                    exception.getMessage());
        }

    }

    protected State getServerCpuLoadState() {

        State state = UnDefType.UNDEF;

        try {
            if ((channelCpuLoad != "") && (isConnected())) {
                state = new DecimalType(new BigDecimal(channelCpuLoad));
            }

        } catch (Exception ex) {
            // Deliberately kept as debug info!
            logger.debug("{}: Exception='{}'", getLogIdentifier(), ex.getMessage());
        }

        return state;
    }

    protected State getServerDiskUsageState() {

        State state = UnDefType.UNDEF;

        try {
            if ((channelDiskUsage != "") && (isConnected())) {
                state = new DecimalType(new BigDecimal(channelDiskUsage));
            }
        } catch (Exception ex) {
            // Deliberately kept as debug info!
            logger.debug("{}: Exception {}", getLogIdentifier(), ex.getMessage());
        }

        return state;
    }

    @Override
    public void onBridgeConnected(ZoneMinderServerBridgeHandler bridge, IZoneMinderConnectionInfo connection) {
        logger.info("{}: Brigde went ONLINE", getLogIdentifier());

        try {
            // Start the discovery service
            if (discoveryService == null) {
                discoveryService = new ZoneMinderDiscoveryService(this, 30);
            }

            // TODO:: Check if discovery is enabled
            discoveryService.activate();

            if (discoveryRegistration == null) {
                // And register it as an OSGi service
                discoveryRegistration = bundleContext.registerService(DiscoveryService.class.getName(),
                        discoveryService, new Hashtable<String, Object>());
            }
        } catch (Exception e) {
            logger.error("BRIDGE [{}]: Exception occurred when starting discovery service Exception='{}'", getThingId(),
                    e.getMessage());

        }

        if (taskRefreshData == null) {

            // Perform first refresh manually (we want to force update of DiskUsage)
            boolean updateDiskUsage = (getBridgeConfig().getRefreshIntervalLowPriorityTask() > 0) ? true : false;
            refreshThing(updateDiskUsage);

            if (getBridgeConfig().getRefreshIntervalLowPriorityTask() != 0) {
                refreshFrequency = calculateCommonRefreshFrequency(getBridgeConfig().getRefreshInterval());
            } else {
                refreshFrequency = getBridgeConfig().getRefreshInterval();
            }
            logger.info("BRIDGE [{}]: Calculated refresh inetrval to '{}'", getThingId(), refreshFrequency);

            if (taskRefreshData != null) {
                taskRefreshData.cancel(true);
                taskRefreshData = null;
            }

            // Start job to handle next updates
            taskRefreshData = startTask(refreshDataRunnable, refreshFrequency, refreshFrequency, TimeUnit.SECONDS);

            if (taskPriorityRefreshData != null) {
                taskPriorityRefreshData.cancel(true);
                taskPriorityRefreshData = null;
            }

            // Only start if Priority Frequency is higher than ordinary
            if (refreshFrequency > 1) {
                taskPriorityRefreshData = startTask(refreshPriorityDataRunnable, 0, 1, TimeUnit.SECONDS);
            }
        }

        // Update properties
        updateMonitorProperties();
    }

    @Override
    public void onBridgeDisconnected(ZoneMinderServerBridgeHandler bridge) {
        logger.info("{}: Brigde went OFFLINE", getLogIdentifier());

        // Deactivate discovery service
        discoveryService.deactivate();

        // Stopping refresh thread while OFFLINE
        if (taskRefreshData != null) {
            taskRefreshData.cancel(true);
            taskRefreshData = null;
            logger.debug("{}: Stopping DataRefresh task", getLogIdentifier());
        }

        // Stopping High priority thread while OFFLINE
        if (taskPriorityRefreshData != null) {
            taskPriorityRefreshData.cancel(true);
            taskPriorityRefreshData = null;
            logger.debug("{}: Stopping Priority DataRefresh task", getLogIdentifier());
        }

        // Make sure everything gets refreshed
        for (Channel ch : getThing().getChannels()) {
            handleCommand(ch.getUID(), RefreshType.REFRESH);
        }

        // Inform thing handlers of disconnection
        for (Thing thing : getThing().getThings()) {
            ZoneMinderBaseThingHandler thingHandler = (ZoneMinderBaseThingHandler) thing.getHandler();

            if (thingHandler != null) {
                thingHandler.onBridgeDisconnected(this);
                logger.debug("{}: onDisconnected(): Bridge - {}, Thing - {}, Thing Handler - {}", getLogIdentifier(),
                        thing.getBridgeUID(), thing.getUID(), thingHandler);
            }
        }

    }

    /**
     * Method to start a data refresh task.
     */
    protected ScheduledFuture<?> startTask(Runnable command, long delay, long interval, TimeUnit unit) {
        logger.debug("BRIDGE [{}]: Starting ZoneMinder Bridge Monitor Task. Command='{}'", getThingId(),
                command.toString());
        if (interval == 0) {
            return null;
        }

        return scheduler.scheduleWithFixedDelay(command, delay, interval, unit);
    }

    /**
     * Method to stop the datarefresh task.
     */
    protected void stopTask(ScheduledFuture<?> task) {
        try {
            if (task != null && !task.isCancelled()) {
                logger.debug("{}: Stopping ZoneMinder Bridge Monitor Task. Task='{}'", getLogIdentifier(),
                        task.toString());
                task.cancel(true);
            }
        } catch (Exception ex) {
        }

    }

    public ArrayList<IZoneMinderMonitorData> getMonitors() {
        if (isOnline()) {

            try {
                IZoneMinderServer serverProxy = ZoneMinderFactory.getServerProxy(aquireSession());
                processZoneMinderQueryLog(ZoneMinderFactory.getLogEntries(zoneMinderLoggerUuid));
                ArrayList<IZoneMinderMonitorData> result = serverProxy.getMonitors();
                return result;
            } finally {
                releaseSession();
            }
        }
        return new ArrayList<IZoneMinderMonitorData>();
    }

    /*
     * This is experimental
     * Try to add different properties
     */
    private void updateMonitorProperties() {

        if (!isOnline()) {
            return;
        }

        // Update property information about this device
        Map<String, String> properties = editProperties();

        try {
            IZoneMinderServer serverProxy = ZoneMinderFactory.getServerProxy(aquireSession());

            processZoneMinderQueryLog(ZoneMinderFactory.getLogEntries(zoneMinderLoggerUuid));

            IZoneMinderHostVersion hostVersion = null;

            hostVersion = serverProxy.getHostVersion();
            processZoneMinderQueryLog(ZoneMinderFactory.getLogEntries(zoneMinderLoggerUuid));
            if (hostVersion.getHttpResponseCode() != 200) {
                return;
            }
            ZoneMinderConfig configUseApi = serverProxy.getConfig(ZoneMinderConfigEnum.ZM_OPT_USE_API);
            processZoneMinderQueryLog(ZoneMinderFactory.getLogEntries(zoneMinderLoggerUuid));

            ZoneMinderConfig configUseAuth = serverProxy.getConfig(ZoneMinderConfigEnum.ZM_OPT_USE_AUTH);
            processZoneMinderQueryLog(ZoneMinderFactory.getLogEntries(zoneMinderLoggerUuid));

            ZoneMinderConfig configTrigerrs = serverProxy.getConfig(ZoneMinderConfigEnum.ZM_OPT_TRIGGERS);
            processZoneMinderQueryLog(ZoneMinderFactory.getLogEntries(zoneMinderLoggerUuid));

            properties.put(ZoneMinderProperties.PROPERTY_SERVER_VERSION, hostVersion.getVersion());
            properties.put(ZoneMinderProperties.PROPERTY_SERVER_API_VERSION, hostVersion.getApiVersion());
            properties.put(ZoneMinderProperties.PROPERTY_SERVER_USE_API, configUseApi.getValueAsString());
            properties.put(ZoneMinderProperties.PROPERTY_SERVER_USE_AUTHENTIFICATION, configUseAuth.getValueAsString());
            properties.put(ZoneMinderProperties.PROPERTY_SERVER_TRIGGERS_ENABLED, configTrigerrs.getValueAsString());
        } catch (FailedLoginException | ZoneMinderUrlNotFoundException | IOException e) {
            logger.warn("{}: Exception occurred when updating monitor properties (Exception='{}'", getLogIdentifier(),
                    e.getMessage());
        } finally {
            releaseSession();
        }

        // Must loop over the new properties since we might have added data
        boolean update = false;
        Map<String, String> originalProperties = editProperties();
        for (String property : properties.keySet()) {
            if ((originalProperties.get(property) == null
                    || !originalProperties.get(property).equals(properties.get(property)))) {
                update = true;
                break;
            }
        }

        if (update) {
            logger.info("{}: Properties synchronised, Thing id: {}", getLogIdentifier(), getThingId());
            updateProperties(properties);
        }
    }

    @Override
    public String getLogIdentifier() {
        String result = "[BRIDGE]";
        try {
            result = String.format("[BRIDGE (%s)]", getThingId());
        } catch (Exception e) {
            result = "[BRIDGE (?)]";
        }
        return result;
    }
}
