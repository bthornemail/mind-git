/**
 * Fly Controls Component
 * Provides first-person flying controls for 3D navigation
 */
import React, { useRef, useEffect } from 'react';
import { useThree, useFrame } from '@react-three/fiber';
import { FlyControls as ThreeFlyControls } from 'three/examples/jsm/controls/FlyControls.js';
import * as THREE from 'three';

interface FlyControlsProps {
  enabled?: boolean;
  movementSpeed?: number;
  rollSpeed?: number;
  dragToLook?: boolean;
  autoForward?: boolean;
  onControlChange?: (position: THREE.Vector3, rotation: THREE.Euler) => void;
}

export const FlyControls: React.FC<FlyControlsProps> = ({
  enabled = true,
  movementSpeed = 1,
  rollSpeed = 0.005,
  dragToLook = false,
  autoForward = false,
  onControlChange
}) => {
  const { camera, gl } = useThree();
  const controlsRef = useRef<ThreeFlyControls>();
  const previousPosition = useRef<THREE.Vector3>(new THREE.Vector3());
  const previousRotation = useRef<THREE.Euler>(new THREE.Euler());

  useEffect(() => {
    if (!camera || !gl) return;

    const controls = new ThreeFlyControls(camera, gl.domElement);
    controlsRef.current = controls;

    // Configure controls
    controls.movementSpeed = movementSpeed;
    controls.rollSpeed = rollSpeed;
    controls.dragToLook = dragToLook;
    controls.autoForward = autoForward;

    // Store initial position and rotation
    previousPosition.current.copy(camera.position);
    previousRotation.current.copy(camera.rotation);

    return () => {
      controls.dispose();
    };
  }, [camera, gl, movementSpeed, rollSpeed, dragToLook, autoForward]);

  useEffect(() => {
    if (controlsRef.current) {
      controlsRef.current.enabled = enabled;
    }
  }, [enabled]);

  // Update controls and check for changes
  useFrame((state, delta) => {
    if (controlsRef.current && enabled) {
      controlsRef.current.update(delta);

      // Check if position or rotation changed
      const positionChanged = !camera.position.equals(previousPosition.current);
      const rotationChanged = !camera.rotation.equals(previousRotation.current);

      if (positionChanged || rotationChanged) {
        previousPosition.current.copy(camera.position);
        previousRotation.current.copy(camera.rotation);

        if (onControlChange) {
          onControlChange(camera.position.clone(), camera.rotation.clone());
        }
      }
    }
  });

  return null;
};